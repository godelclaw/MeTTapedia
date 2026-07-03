import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoTMLargeFiberBridgeBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for `normal,mirror` size-64 fiber 70

This module proves direct connectedness for one generated size-64 fiber
whose parent order needs multiple closure scans. It is generated from
row-local reverse certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoTMLargeFiberBridge

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate
open GoertzelLemma818TauMirrorCertificate
open GoertzelLemma818TauMirrorReverseAudit

def tmFiber70StateAt (i : Nat) : List TauState :=
  directStates (tmFiber70RowAt i).sourceLeft (tmFiber70RowAt i).sourceRight

def tmFiber70DirectStates : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]

def tmFiber70Prefix0 : List (List TauState) :=
  [tmFiber70StateAt 0]

def tmFiber70Prefix1 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1]

def tmFiber70Prefix2 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2]

def tmFiber70Prefix3 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3]

def tmFiber70Prefix4 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4]

def tmFiber70Prefix5 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5]

def tmFiber70Prefix6 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6]

def tmFiber70Prefix7 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7]

def tmFiber70Prefix8 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8]

def tmFiber70Prefix9 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9]

def tmFiber70Prefix10 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10]

def tmFiber70Prefix11 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11]

def tmFiber70Prefix12 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12]

def tmFiber70Prefix13 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13]

def tmFiber70Prefix14 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14]

def tmFiber70Prefix15 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15]

def tmFiber70Prefix16 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16]

def tmFiber70Prefix17 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17]

def tmFiber70Prefix18 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18]

def tmFiber70Prefix19 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19]

def tmFiber70Prefix20 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20]

def tmFiber70Prefix21 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21]

def tmFiber70Prefix22 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22]

def tmFiber70Prefix23 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23]

def tmFiber70Prefix24 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24]

def tmFiber70Prefix25 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25]

def tmFiber70Prefix26 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26]

def tmFiber70Prefix27 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27]

def tmFiber70Prefix28 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28]

def tmFiber70Prefix29 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29]

def tmFiber70Prefix30 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30]

def tmFiber70Prefix31 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31]

def tmFiber70Prefix32 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32]

def tmFiber70Prefix33 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33]

def tmFiber70Prefix34 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34]

def tmFiber70Prefix35 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35]

def tmFiber70Prefix36 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36]

def tmFiber70Prefix37 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37]

def tmFiber70Prefix38 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38]

def tmFiber70Prefix39 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39]

def tmFiber70Prefix40 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40]

def tmFiber70Prefix41 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41]

def tmFiber70Prefix42 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42]

def tmFiber70Prefix43 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43]

def tmFiber70Prefix44 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44]

def tmFiber70Prefix45 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45]

def tmFiber70Prefix46 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46]

def tmFiber70Prefix47 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47]

def tmFiber70Prefix48 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48]

def tmFiber70Prefix49 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49]

def tmFiber70Prefix50 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50]

def tmFiber70Prefix51 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51]

def tmFiber70Prefix52 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52]

def tmFiber70Prefix53 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53]

def tmFiber70Prefix54 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54]

def tmFiber70Prefix55 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55]

def tmFiber70Prefix56 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56]

def tmFiber70Prefix57 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57]

def tmFiber70Prefix58 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58]

def tmFiber70Prefix59 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59]

def tmFiber70Prefix60 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60]

def tmFiber70Prefix61 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61]

def tmFiber70Prefix62 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62]

def tmFiber70Prefix63 : List (List TauState) :=
  [tmFiber70StateAt 0, tmFiber70StateAt 1, tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]

theorem tmFiber70ReverseRow_1_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 1) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk0_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 0) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 1)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep1 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 1) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 1)
    (tmFiber70RowAt 1).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 1) (by decide) tmFiber70ReverseRow_1_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_2_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 2) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk1_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 2) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep2 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 2) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 2)
    (tmFiber70RowAt 2).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 2) (by decide) tmFiber70ReverseRow_2_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_3_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 3) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk1_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 2) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 3)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep3 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 3) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 3)
    (tmFiber70RowAt 3).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 3) (by decide) tmFiber70ReverseRow_3_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_4_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 4) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk2_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 4) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep4 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 4) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 4)
    (tmFiber70RowAt 4).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 4) (by decide) tmFiber70ReverseRow_4_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_5_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 5) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk2_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 4) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 5)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep5 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 5) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 5)
    (tmFiber70RowAt 5).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 5) (by decide) tmFiber70ReverseRow_5_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_6_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 6) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk3_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 6) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep6 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 6) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 6)
    (tmFiber70RowAt 6).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 6) (by decide) tmFiber70ReverseRow_6_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_7_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 7) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk3_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 6) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 7)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep7 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 7) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 7)
    (tmFiber70RowAt 7).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 7) (by decide) tmFiber70ReverseRow_7_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_8_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 8) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk4_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 8) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep8 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 8) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 8)
    (tmFiber70RowAt 8).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 8) (by decide) tmFiber70ReverseRow_8_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_9_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 9) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk4_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 8) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 9)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep9 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 9) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 9)
    (tmFiber70RowAt 9).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 9) (by decide) tmFiber70ReverseRow_9_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_10_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 10) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk5_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 10) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep10 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 10) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 10)
    (tmFiber70RowAt 10).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 10) (by decide) tmFiber70ReverseRow_10_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_11_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 11) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk5_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 10) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 11)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep11 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 11) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 11)
    (tmFiber70RowAt 11).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 11) (by decide) tmFiber70ReverseRow_11_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_12_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 12) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk6_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 12) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep12 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 12) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 12)
    (tmFiber70RowAt 12).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 12) (by decide) tmFiber70ReverseRow_12_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_13_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 13) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk6_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 12) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 13)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep13 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 13) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 13)
    (tmFiber70RowAt 13).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 13) (by decide) tmFiber70ReverseRow_13_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_14_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 14) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk7_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 14) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep14 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 6) (tmFiber70StateAt 14) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 6) (tmFiber70StateAt 14)
    (tmFiber70RowAt 14).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 14) (by decide) tmFiber70ReverseRow_14_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_15_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 15) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk7_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 14) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 15)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep15 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 7) (tmFiber70StateAt 15) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 7) (tmFiber70StateAt 15)
    (tmFiber70RowAt 15).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 15) (by decide) tmFiber70ReverseRow_15_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_16_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 16) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk8_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 16) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep16 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 16) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 16)
    (tmFiber70RowAt 16).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 16) (by decide) tmFiber70ReverseRow_16_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_17_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 17) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk8_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 16) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 17)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep17 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 17) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 17)
    (tmFiber70RowAt 17).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 17) (by decide) tmFiber70ReverseRow_17_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_18_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 18) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk9_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 18) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep18 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 18) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 18)
    (tmFiber70RowAt 18).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 18) (by decide) tmFiber70ReverseRow_18_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_19_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 19) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk9_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 18) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 19)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep19 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 19) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 19)
    (tmFiber70RowAt 19).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 19) (by decide) tmFiber70ReverseRow_19_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_20_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 20) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk10_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 20) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep20 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 20) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 20)
    (tmFiber70RowAt 20).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 20) (by decide) tmFiber70ReverseRow_20_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_21_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 21) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk10_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 20) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 21)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep21 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 21) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 21)
    (tmFiber70RowAt 21).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 21) (by decide) tmFiber70ReverseRow_21_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_22_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 22) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk11_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 22) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep22 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 6) (tmFiber70StateAt 22) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 6) (tmFiber70StateAt 22)
    (tmFiber70RowAt 22).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 22) (by decide) tmFiber70ReverseRow_22_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_23_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 23) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk11_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 22) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 23)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep23 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 7) (tmFiber70StateAt 23) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 7) (tmFiber70StateAt 23)
    (tmFiber70RowAt 23).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 23) (by decide) tmFiber70ReverseRow_23_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_24_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 24) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk12_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 24) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep24 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 8) (tmFiber70StateAt 24) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 8) (tmFiber70StateAt 24)
    (tmFiber70RowAt 24).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 24) (by decide) tmFiber70ReverseRow_24_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_25_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 25) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk12_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 24) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 25)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep25 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 9) (tmFiber70StateAt 25) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 9) (tmFiber70StateAt 25)
    (tmFiber70RowAt 25).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 25) (by decide) tmFiber70ReverseRow_25_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_26_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 26) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk13_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 26) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep26 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 10) (tmFiber70StateAt 26) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 10) (tmFiber70StateAt 26)
    (tmFiber70RowAt 26).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 26) (by decide) tmFiber70ReverseRow_26_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_27_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 27) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk13_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 26) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 27)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep27 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 11) (tmFiber70StateAt 27) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 11) (tmFiber70StateAt 27)
    (tmFiber70RowAt 27).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 27) (by decide) tmFiber70ReverseRow_27_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_28_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 28) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk14_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 28) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep28 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 12) (tmFiber70StateAt 28) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 12) (tmFiber70StateAt 28)
    (tmFiber70RowAt 28).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 28) (by decide) tmFiber70ReverseRow_28_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_29_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 29) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk14_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 28) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 29)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep29 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 13) (tmFiber70StateAt 29) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 13) (tmFiber70StateAt 29)
    (tmFiber70RowAt 29).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 29) (by decide) tmFiber70ReverseRow_29_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_30_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 30) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk15_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 30) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep30 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 14) (tmFiber70StateAt 30) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 14) (tmFiber70StateAt 30)
    (tmFiber70RowAt 30).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 30) (by decide) tmFiber70ReverseRow_30_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_31_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 31) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk15_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 30) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 31)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep31 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 15) (tmFiber70StateAt 31) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 15) (tmFiber70StateAt 31)
    (tmFiber70RowAt 31).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 31) (by decide) tmFiber70ReverseRow_31_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_32_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 32) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk16_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 32) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep32 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 36) (tmFiber70StateAt 32) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 36) (tmFiber70StateAt 32)
    (tmFiber70RowAt 32).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 32) (by decide) tmFiber70ReverseRow_32_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_33_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 33) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk16_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 32) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 33)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep33 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 37) (tmFiber70StateAt 33) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 37) (tmFiber70StateAt 33)
    (tmFiber70RowAt 33).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 33) (by decide) tmFiber70ReverseRow_33_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_34_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 34) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk17_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 34) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep34 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 20) (tmFiber70StateAt 34) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 20) (tmFiber70StateAt 34)
    (tmFiber70RowAt 34).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 34) (by decide) tmFiber70ReverseRow_34_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_35_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 35) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk17_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 34) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 35)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep35 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 21) (tmFiber70StateAt 35) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 21) (tmFiber70StateAt 35)
    (tmFiber70RowAt 35).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 35) (by decide) tmFiber70ReverseRow_35_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_36_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 36) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk18_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 36) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep36 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 16) (tmFiber70StateAt 36) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 16) (tmFiber70StateAt 36)
    (tmFiber70RowAt 36).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 36) (by decide) tmFiber70ReverseRow_36_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_37_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 37) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk18_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 36) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 37)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep37 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 17) (tmFiber70StateAt 37) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 17) (tmFiber70StateAt 37)
    (tmFiber70RowAt 37).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 37) (by decide) tmFiber70ReverseRow_37_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_38_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 38) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk19_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 38) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep38 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 18) (tmFiber70StateAt 38) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 18) (tmFiber70StateAt 38)
    (tmFiber70RowAt 38).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 38) (by decide) tmFiber70ReverseRow_38_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_39_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 39) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk19_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 38) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 39)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep39 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 19) (tmFiber70StateAt 39) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 19) (tmFiber70StateAt 39)
    (tmFiber70RowAt 39).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 39) (by decide) tmFiber70ReverseRow_39_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_40_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 40) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk20_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 40) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep40 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 44) (tmFiber70StateAt 40) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 44) (tmFiber70StateAt 40)
    (tmFiber70RowAt 40).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 40) (by decide) tmFiber70ReverseRow_40_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_41_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 41) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk20_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 40) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 41)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep41 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 45) (tmFiber70StateAt 41) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 45) (tmFiber70StateAt 41)
    (tmFiber70RowAt 41).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 41) (by decide) tmFiber70ReverseRow_41_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_42_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 42) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk21_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 42) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep42 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 58) (tmFiber70StateAt 42) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 58) (tmFiber70StateAt 42)
    (tmFiber70RowAt 42).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 42) (by decide) tmFiber70ReverseRow_42_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_43_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 43) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk21_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 42) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 43)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep43 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 59) (tmFiber70StateAt 43) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 59) (tmFiber70StateAt 43)
    (tmFiber70RowAt 43).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 43) (by decide) tmFiber70ReverseRow_43_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_44_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 44) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk22_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 44) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep44 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 60) (tmFiber70StateAt 44) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 60) (tmFiber70StateAt 44)
    (tmFiber70RowAt 44).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 44) (by decide) tmFiber70ReverseRow_44_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_45_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 45) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk22_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 44) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 45)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep45 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 61) (tmFiber70StateAt 45) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 61) (tmFiber70StateAt 45)
    (tmFiber70RowAt 45).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 45) (by decide) tmFiber70ReverseRow_45_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_46_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 46) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk23_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 46) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep46 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 62) (tmFiber70StateAt 46) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 62) (tmFiber70StateAt 46)
    (tmFiber70RowAt 46).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 46) (by decide) tmFiber70ReverseRow_46_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_47_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 47) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk23_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 46) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 47)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep47 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 63) (tmFiber70StateAt 47) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 63) (tmFiber70StateAt 47)
    (tmFiber70RowAt 47).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 47) (by decide) tmFiber70ReverseRow_47_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_48_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 48) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk24_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 48) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep48 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 52) (tmFiber70StateAt 48) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 52) (tmFiber70StateAt 48)
    (tmFiber70RowAt 48).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 48) (by decide) tmFiber70ReverseRow_48_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_49_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 49) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk24_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 48) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 49)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep49 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 53) (tmFiber70StateAt 49) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 53) (tmFiber70StateAt 49)
    (tmFiber70RowAt 49).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 49) (by decide) tmFiber70ReverseRow_49_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_50_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 50) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk25_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 50) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep50 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 12) (tmFiber70StateAt 50) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 12) (tmFiber70StateAt 50)
    (tmFiber70RowAt 50).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 50) (by decide) tmFiber70ReverseRow_50_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_51_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 51) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk25_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 50) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 51)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep51 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 13) (tmFiber70StateAt 51) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 13) (tmFiber70StateAt 51)
    (tmFiber70RowAt 51).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 51) (by decide) tmFiber70ReverseRow_51_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_52_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 52) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk26_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 52) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep52 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 8) (tmFiber70StateAt 52) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 8) (tmFiber70StateAt 52)
    (tmFiber70RowAt 52).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 52) (by decide) tmFiber70ReverseRow_52_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_53_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 53) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk26_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 52) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 53)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep53 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 9) (tmFiber70StateAt 53) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 9) (tmFiber70StateAt 53)
    (tmFiber70RowAt 53).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 53) (by decide) tmFiber70ReverseRow_53_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_54_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 54) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk27_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 54) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep54 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 10) (tmFiber70StateAt 54) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 10) (tmFiber70StateAt 54)
    (tmFiber70RowAt 54).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 54) (by decide) tmFiber70ReverseRow_54_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_55_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 55) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk27_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 54) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 55)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep55 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 11) (tmFiber70StateAt 55) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 11) (tmFiber70StateAt 55)
    (tmFiber70RowAt 55).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 55) (by decide) tmFiber70ReverseRow_55_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_56_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 56) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk28_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 56) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep56 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 60) (tmFiber70StateAt 56) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 60) (tmFiber70StateAt 56)
    (tmFiber70RowAt 56).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 56) (by decide) tmFiber70ReverseRow_56_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_57_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 57) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk28_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 56) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 57)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep57 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 61) (tmFiber70StateAt 57) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 61) (tmFiber70StateAt 57)
    (tmFiber70RowAt 57).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 57) (by decide) tmFiber70ReverseRow_57_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_58_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 58) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk29_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 58) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep58 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 58) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 4) (tmFiber70StateAt 58)
    (tmFiber70RowAt 58).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 58) (by decide) tmFiber70ReverseRow_58_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_59_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 59) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk29_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 58) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 59)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep59 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 59) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 5) (tmFiber70StateAt 59)
    (tmFiber70RowAt 59).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 59) (by decide) tmFiber70ReverseRow_59_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_60_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 60) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk30_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 60) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep60 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 60) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 0) (tmFiber70StateAt 60)
    (tmFiber70RowAt 60).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 60) (by decide) tmFiber70ReverseRow_60_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_61_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 61) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk30_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 60) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 61)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep61 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 61) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 1) (tmFiber70StateAt 61)
    (tmFiber70RowAt 61).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 61) (by decide) tmFiber70ReverseRow_61_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_62_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 62) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk31_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 62) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).1

theorem tmFiber70ReverseSingleStep62 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 62) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 2) (tmFiber70StateAt 62)
    (tmFiber70RowAt 62).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 62) (by decide) tmFiber70ReverseRow_62_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70ReverseRow_63_ok :
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 63) = true := by
  have h := GoertzelLemma818TauMirrorReverseAudit.tmReverseFiber70Chunk31_ok
  change (tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 62) &&
    tmRowReverseValid tmFiber70Key tmFiber70Expected (tmFiber70RowAt 63)) = true at h
  exact (Bool.and_eq_true_iff.mp h).2

theorem tmFiber70ReverseSingleStep63 :
    chainSingleKempeStep tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 63) = true :=
  chainSpecifiedKempeStep_implies_single tmWord (tmFiber70StateAt 3) (tmFiber70StateAt 63)
    (tmFiber70RowAt 63).move (by decide) (by decide) (by
      have h := tmRowReverseValid_step_of_ne tmFiber70Key tmFiber70Expected
        (tmFiber70RowAt 63) (by decide) tmFiber70ReverseRow_63_ok
      simpa [tmFiber70StateAt, tmFiber70RowAt, tmFiber70Rows, listGetD, directRow] using h)

theorem tmFiber70State1_in_pass1_prefix1 :
    tmFiber70StateAt 1 ∈ chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix0 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix0
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix1 = tmFiber70Prefix0 ++ [tmFiber70StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 1) []
    (chainClosureStep tmWord tmFiber70Prefix0 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep1

theorem tmFiber70State1_in_pass1_full :
    tmFiber70StateAt 1 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix1 ++ [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1

theorem tmFiber70State2_in_pass1_prefix2 :
    tmFiber70StateAt 2 ∈ chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix1 = tmFiber70Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord []
      (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1
  rw [show tmFiber70Prefix2 = tmFiber70Prefix1 ++ [tmFiber70StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 2) []
    (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) hparentBefore tmFiber70ReverseSingleStep2

theorem tmFiber70State2_in_pass1_full :
    tmFiber70StateAt 2 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix2 ++ [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 2) tmFiber70State2_in_pass1_prefix2

theorem tmFiber70State3_in_pass1_prefix3 :
    tmFiber70StateAt 3 ∈ chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix2
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix3 = tmFiber70Prefix2 ++ [tmFiber70StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 3) []
    (chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep3

theorem tmFiber70State3_in_pass1_full :
    tmFiber70StateAt 3 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix3 ++ [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 3) tmFiber70State3_in_pass1_prefix3

theorem tmFiber70State4_in_pass1_prefix4 :
    tmFiber70StateAt 4 ∈ chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix3
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix4 = tmFiber70Prefix3 ++ [tmFiber70StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 4) []
    (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep4

theorem tmFiber70State4_in_pass1_full :
    tmFiber70StateAt 4 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix4 ++ [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 4) tmFiber70State4_in_pass1_prefix4

theorem tmFiber70State5_in_pass1_prefix5 :
    tmFiber70StateAt 5 ∈ chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix4 = tmFiber70Prefix1 ++ [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4]
      (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1
  rw [show tmFiber70Prefix5 = tmFiber70Prefix4 ++ [tmFiber70StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 5) []
    (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) hparentBefore tmFiber70ReverseSingleStep5

theorem tmFiber70State5_in_pass1_full :
    tmFiber70StateAt 5 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix5 ++ [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 5) tmFiber70State5_in_pass1_prefix5

theorem tmFiber70State6_in_pass1_prefix6 :
    tmFiber70StateAt 6 ∈ chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 4 ∈
      chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix5 = tmFiber70Prefix4 ++ [tmFiber70StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 5]
      (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 4) tmFiber70State4_in_pass1_prefix4
  rw [show tmFiber70Prefix6 = tmFiber70Prefix5 ++ [tmFiber70StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 6) []
    (chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 4) hparentBefore tmFiber70ReverseSingleStep6

theorem tmFiber70State6_in_pass1_full :
    tmFiber70StateAt 6 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix6 ++ [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 6) tmFiber70State6_in_pass1_prefix6

theorem tmFiber70State7_in_pass1_prefix7 :
    tmFiber70StateAt 7 ∈ chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 3 ∈
      chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix6 = tmFiber70Prefix3 ++ [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6]
      (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 3) tmFiber70State3_in_pass1_prefix3
  rw [show tmFiber70Prefix7 = tmFiber70Prefix6 ++ [tmFiber70StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 7) []
    (chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 3) hparentBefore tmFiber70ReverseSingleStep7

theorem tmFiber70State7_in_pass1_full :
    tmFiber70StateAt 7 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix7 ++ [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 7) tmFiber70State7_in_pass1_prefix7

theorem tmFiber70State8_in_pass1_prefix8 :
    tmFiber70StateAt 8 ∈ chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix7
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix8 = tmFiber70Prefix7 ++ [tmFiber70StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 8) []
    (chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep8

theorem tmFiber70State8_in_pass1_full :
    tmFiber70StateAt 8 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix8 ++ [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 8) tmFiber70State8_in_pass1_prefix8

theorem tmFiber70State9_in_pass1_prefix9 :
    tmFiber70StateAt 9 ∈ chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix8 = tmFiber70Prefix1 ++ [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8]
      (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1
  rw [show tmFiber70Prefix9 = tmFiber70Prefix8 ++ [tmFiber70StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 9) []
    (chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) hparentBefore tmFiber70ReverseSingleStep9

theorem tmFiber70State9_in_pass1_full :
    tmFiber70StateAt 9 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix9 ++ [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 9) tmFiber70State9_in_pass1_prefix9

theorem tmFiber70State10_in_pass1_prefix10 :
    tmFiber70StateAt 10 ∈ chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 2 ∈
      chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix9 = tmFiber70Prefix2 ++ [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9]
      (chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 2) tmFiber70State2_in_pass1_prefix2
  rw [show tmFiber70Prefix10 = tmFiber70Prefix9 ++ [tmFiber70StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 10) []
    (chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 2) hparentBefore tmFiber70ReverseSingleStep10

theorem tmFiber70State10_in_pass1_full :
    tmFiber70StateAt 10 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix10 ++ [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 10) tmFiber70State10_in_pass1_prefix10

theorem tmFiber70State11_in_pass1_prefix11 :
    tmFiber70StateAt 11 ∈ chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 3 ∈
      chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix10 = tmFiber70Prefix3 ++ [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10]
      (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 3) tmFiber70State3_in_pass1_prefix3
  rw [show tmFiber70Prefix11 = tmFiber70Prefix10 ++ [tmFiber70StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 11) []
    (chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 3) hparentBefore tmFiber70ReverseSingleStep11

theorem tmFiber70State11_in_pass1_full :
    tmFiber70StateAt 11 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix11 ++ [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 11) tmFiber70State11_in_pass1_prefix11

theorem tmFiber70State12_in_pass1_prefix12 :
    tmFiber70StateAt 12 ∈ chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 4 ∈
      chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix11 = tmFiber70Prefix4 ++ [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11]
      (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 4) tmFiber70State4_in_pass1_prefix4
  rw [show tmFiber70Prefix12 = tmFiber70Prefix11 ++ [tmFiber70StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 12) []
    (chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 4) hparentBefore tmFiber70ReverseSingleStep12

theorem tmFiber70State12_in_pass1_full :
    tmFiber70StateAt 12 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix12 ++ [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 12) tmFiber70State12_in_pass1_prefix12

theorem tmFiber70State13_in_pass1_prefix13 :
    tmFiber70StateAt 13 ∈ chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 5 ∈
      chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix12 = tmFiber70Prefix5 ++ [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12]
      (chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 5) tmFiber70State5_in_pass1_prefix5
  rw [show tmFiber70Prefix13 = tmFiber70Prefix12 ++ [tmFiber70StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 13) []
    (chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 5) hparentBefore tmFiber70ReverseSingleStep13

theorem tmFiber70State13_in_pass1_full :
    tmFiber70StateAt 13 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix13 ++ [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 13) tmFiber70State13_in_pass1_prefix13

theorem tmFiber70State14_in_pass1_prefix14 :
    tmFiber70StateAt 14 ∈ chainClosureStep tmWord tmFiber70Prefix14 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 6 ∈
      chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix13 = tmFiber70Prefix6 ++ [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13]
      (chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 6) tmFiber70State6_in_pass1_prefix6
  rw [show tmFiber70Prefix14 = tmFiber70Prefix13 ++ [tmFiber70StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 14) []
    (chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 6) hparentBefore tmFiber70ReverseSingleStep14

theorem tmFiber70State14_in_pass1_full :
    tmFiber70StateAt 14 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix14 ++ [tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix14 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 14) tmFiber70State14_in_pass1_prefix14

theorem tmFiber70State15_in_pass1_prefix15 :
    tmFiber70StateAt 15 ∈ chainClosureStep tmWord tmFiber70Prefix15 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 7 ∈
      chainClosureStep tmWord tmFiber70Prefix14 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix14 = tmFiber70Prefix7 ++ [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14]
      (chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 7) tmFiber70State7_in_pass1_prefix7
  rw [show tmFiber70Prefix15 = tmFiber70Prefix14 ++ [tmFiber70StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 15) []
    (chainClosureStep tmWord tmFiber70Prefix14 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 7) hparentBefore tmFiber70ReverseSingleStep15

theorem tmFiber70State15_in_pass1_full :
    tmFiber70StateAt 15 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix15 ++ [tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix15 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 15) tmFiber70State15_in_pass1_prefix15

theorem tmFiber70State16_in_pass1_prefix16 :
    tmFiber70StateAt 16 ∈ chainClosureStep tmWord tmFiber70Prefix16 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix15 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix15
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix16 = tmFiber70Prefix15 ++ [tmFiber70StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 16) []
    (chainClosureStep tmWord tmFiber70Prefix15 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep16

theorem tmFiber70State16_in_pass1_full :
    tmFiber70StateAt 16 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix16 ++ [tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix16 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 16) tmFiber70State16_in_pass1_prefix16

theorem tmFiber70State17_in_pass1_prefix17 :
    tmFiber70StateAt 17 ∈ chainClosureStep tmWord tmFiber70Prefix17 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70Prefix16 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix16 = tmFiber70Prefix1 ++ [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16]
      (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1
  rw [show tmFiber70Prefix17 = tmFiber70Prefix16 ++ [tmFiber70StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 17) []
    (chainClosureStep tmWord tmFiber70Prefix16 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) hparentBefore tmFiber70ReverseSingleStep17

theorem tmFiber70State17_in_pass1_full :
    tmFiber70StateAt 17 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix17 ++ [tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix17 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 17) tmFiber70State17_in_pass1_prefix17

theorem tmFiber70State18_in_pass1_prefix18 :
    tmFiber70StateAt 18 ∈ chainClosureStep tmWord tmFiber70Prefix18 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 2 ∈
      chainClosureStep tmWord tmFiber70Prefix17 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix17 = tmFiber70Prefix2 ++ [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17]
      (chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 2) tmFiber70State2_in_pass1_prefix2
  rw [show tmFiber70Prefix18 = tmFiber70Prefix17 ++ [tmFiber70StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 18) []
    (chainClosureStep tmWord tmFiber70Prefix17 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 2) hparentBefore tmFiber70ReverseSingleStep18

theorem tmFiber70State18_in_pass1_full :
    tmFiber70StateAt 18 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix18 ++ [tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix18 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 18) tmFiber70State18_in_pass1_prefix18

theorem tmFiber70State19_in_pass1_prefix19 :
    tmFiber70StateAt 19 ∈ chainClosureStep tmWord tmFiber70Prefix19 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 3 ∈
      chainClosureStep tmWord tmFiber70Prefix18 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix18 = tmFiber70Prefix3 ++ [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18]
      (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 3) tmFiber70State3_in_pass1_prefix3
  rw [show tmFiber70Prefix19 = tmFiber70Prefix18 ++ [tmFiber70StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 19) []
    (chainClosureStep tmWord tmFiber70Prefix18 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 3) hparentBefore tmFiber70ReverseSingleStep19

theorem tmFiber70State19_in_pass1_full :
    tmFiber70StateAt 19 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix19 ++ [tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix19 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 19) tmFiber70State19_in_pass1_prefix19

theorem tmFiber70State20_in_pass1_prefix20 :
    tmFiber70StateAt 20 ∈ chainClosureStep tmWord tmFiber70Prefix20 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 4 ∈
      chainClosureStep tmWord tmFiber70Prefix19 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix19 = tmFiber70Prefix4 ++ [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19]
      (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 4) tmFiber70State4_in_pass1_prefix4
  rw [show tmFiber70Prefix20 = tmFiber70Prefix19 ++ [tmFiber70StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 20) []
    (chainClosureStep tmWord tmFiber70Prefix19 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 4) hparentBefore tmFiber70ReverseSingleStep20

theorem tmFiber70State20_in_pass1_full :
    tmFiber70StateAt 20 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix20 ++ [tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix20 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 20) tmFiber70State20_in_pass1_prefix20

theorem tmFiber70State21_in_pass1_prefix21 :
    tmFiber70StateAt 21 ∈ chainClosureStep tmWord tmFiber70Prefix21 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 5 ∈
      chainClosureStep tmWord tmFiber70Prefix20 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix20 = tmFiber70Prefix5 ++ [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20]
      (chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 5) tmFiber70State5_in_pass1_prefix5
  rw [show tmFiber70Prefix21 = tmFiber70Prefix20 ++ [tmFiber70StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 21) []
    (chainClosureStep tmWord tmFiber70Prefix20 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 5) hparentBefore tmFiber70ReverseSingleStep21

theorem tmFiber70State21_in_pass1_full :
    tmFiber70StateAt 21 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix21 ++ [tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix21 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 21) tmFiber70State21_in_pass1_prefix21

theorem tmFiber70State22_in_pass1_prefix22 :
    tmFiber70StateAt 22 ∈ chainClosureStep tmWord tmFiber70Prefix22 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 6 ∈
      chainClosureStep tmWord tmFiber70Prefix21 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix21 = tmFiber70Prefix6 ++ [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21]
      (chainClosureStep tmWord tmFiber70Prefix6 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 6) tmFiber70State6_in_pass1_prefix6
  rw [show tmFiber70Prefix22 = tmFiber70Prefix21 ++ [tmFiber70StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 22) []
    (chainClosureStep tmWord tmFiber70Prefix21 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 6) hparentBefore tmFiber70ReverseSingleStep22

theorem tmFiber70State22_in_pass1_full :
    tmFiber70StateAt 22 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix22 ++ [tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix22 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 22) tmFiber70State22_in_pass1_prefix22

theorem tmFiber70State23_in_pass1_prefix23 :
    tmFiber70StateAt 23 ∈ chainClosureStep tmWord tmFiber70Prefix23 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 7 ∈
      chainClosureStep tmWord tmFiber70Prefix22 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix22 = tmFiber70Prefix7 ++ [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22]
      (chainClosureStep tmWord tmFiber70Prefix7 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 7) tmFiber70State7_in_pass1_prefix7
  rw [show tmFiber70Prefix23 = tmFiber70Prefix22 ++ [tmFiber70StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 23) []
    (chainClosureStep tmWord tmFiber70Prefix22 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 7) hparentBefore tmFiber70ReverseSingleStep23

theorem tmFiber70State23_in_pass1_full :
    tmFiber70StateAt 23 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix23 ++ [tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix23 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 23) tmFiber70State23_in_pass1_prefix23

theorem tmFiber70State24_in_pass1_prefix24 :
    tmFiber70StateAt 24 ∈ chainClosureStep tmWord tmFiber70Prefix24 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 8 ∈
      chainClosureStep tmWord tmFiber70Prefix23 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix23 = tmFiber70Prefix8 ++ [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23]
      (chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 8) tmFiber70State8_in_pass1_prefix8
  rw [show tmFiber70Prefix24 = tmFiber70Prefix23 ++ [tmFiber70StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 24) []
    (chainClosureStep tmWord tmFiber70Prefix23 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 8) hparentBefore tmFiber70ReverseSingleStep24

theorem tmFiber70State24_in_pass1_full :
    tmFiber70StateAt 24 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix24 ++ [tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix24 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 24) tmFiber70State24_in_pass1_prefix24

theorem tmFiber70State25_in_pass1_prefix25 :
    tmFiber70StateAt 25 ∈ chainClosureStep tmWord tmFiber70Prefix25 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 9 ∈
      chainClosureStep tmWord tmFiber70Prefix24 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix24 = tmFiber70Prefix9 ++ [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24]
      (chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 9) tmFiber70State9_in_pass1_prefix9
  rw [show tmFiber70Prefix25 = tmFiber70Prefix24 ++ [tmFiber70StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 25) []
    (chainClosureStep tmWord tmFiber70Prefix24 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 9) hparentBefore tmFiber70ReverseSingleStep25

theorem tmFiber70State25_in_pass1_full :
    tmFiber70StateAt 25 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix25 ++ [tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix25 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 25) tmFiber70State25_in_pass1_prefix25

theorem tmFiber70State26_in_pass1_prefix26 :
    tmFiber70StateAt 26 ∈ chainClosureStep tmWord tmFiber70Prefix26 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 10 ∈
      chainClosureStep tmWord tmFiber70Prefix25 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix25 = tmFiber70Prefix10 ++ [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25]
      (chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 10) tmFiber70State10_in_pass1_prefix10
  rw [show tmFiber70Prefix26 = tmFiber70Prefix25 ++ [tmFiber70StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 26) []
    (chainClosureStep tmWord tmFiber70Prefix25 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 10) hparentBefore tmFiber70ReverseSingleStep26

theorem tmFiber70State26_in_pass1_full :
    tmFiber70StateAt 26 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix26 ++ [tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix26 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 26) tmFiber70State26_in_pass1_prefix26

theorem tmFiber70State27_in_pass1_prefix27 :
    tmFiber70StateAt 27 ∈ chainClosureStep tmWord tmFiber70Prefix27 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 11 ∈
      chainClosureStep tmWord tmFiber70Prefix26 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix26 = tmFiber70Prefix11 ++ [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26]
      (chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 11) tmFiber70State11_in_pass1_prefix11
  rw [show tmFiber70Prefix27 = tmFiber70Prefix26 ++ [tmFiber70StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 27) []
    (chainClosureStep tmWord tmFiber70Prefix26 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 11) hparentBefore tmFiber70ReverseSingleStep27

theorem tmFiber70State27_in_pass1_full :
    tmFiber70StateAt 27 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix27 ++ [tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix27 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 27) tmFiber70State27_in_pass1_prefix27

theorem tmFiber70State28_in_pass1_prefix28 :
    tmFiber70StateAt 28 ∈ chainClosureStep tmWord tmFiber70Prefix28 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 12 ∈
      chainClosureStep tmWord tmFiber70Prefix27 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix27 = tmFiber70Prefix12 ++ [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27]
      (chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 12) tmFiber70State12_in_pass1_prefix12
  rw [show tmFiber70Prefix28 = tmFiber70Prefix27 ++ [tmFiber70StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 28) []
    (chainClosureStep tmWord tmFiber70Prefix27 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 12) hparentBefore tmFiber70ReverseSingleStep28

theorem tmFiber70State28_in_pass1_full :
    tmFiber70StateAt 28 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix28 ++ [tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix28 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 28) tmFiber70State28_in_pass1_prefix28

theorem tmFiber70State29_in_pass1_prefix29 :
    tmFiber70StateAt 29 ∈ chainClosureStep tmWord tmFiber70Prefix29 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 13 ∈
      chainClosureStep tmWord tmFiber70Prefix28 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix28 = tmFiber70Prefix13 ++ [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28]
      (chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 13) tmFiber70State13_in_pass1_prefix13
  rw [show tmFiber70Prefix29 = tmFiber70Prefix28 ++ [tmFiber70StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 29) []
    (chainClosureStep tmWord tmFiber70Prefix28 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 13) hparentBefore tmFiber70ReverseSingleStep29

theorem tmFiber70State29_in_pass1_full :
    tmFiber70StateAt 29 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix29 ++ [tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix29 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 29) tmFiber70State29_in_pass1_prefix29

theorem tmFiber70State30_in_pass1_prefix30 :
    tmFiber70StateAt 30 ∈ chainClosureStep tmWord tmFiber70Prefix30 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 14 ∈
      chainClosureStep tmWord tmFiber70Prefix29 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix29 = tmFiber70Prefix14 ++ [tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29]
      (chainClosureStep tmWord tmFiber70Prefix14 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 14) tmFiber70State14_in_pass1_prefix14
  rw [show tmFiber70Prefix30 = tmFiber70Prefix29 ++ [tmFiber70StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 30) []
    (chainClosureStep tmWord tmFiber70Prefix29 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 14) hparentBefore tmFiber70ReverseSingleStep30

theorem tmFiber70State30_in_pass1_full :
    tmFiber70StateAt 30 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix30 ++ [tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix30 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 30) tmFiber70State30_in_pass1_prefix30

theorem tmFiber70State31_in_pass1_prefix31 :
    tmFiber70StateAt 31 ∈ chainClosureStep tmWord tmFiber70Prefix31 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 15 ∈
      chainClosureStep tmWord tmFiber70Prefix30 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix30 = tmFiber70Prefix15 ++ [tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30]
      (chainClosureStep tmWord tmFiber70Prefix15 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 15) tmFiber70State15_in_pass1_prefix15
  rw [show tmFiber70Prefix31 = tmFiber70Prefix30 ++ [tmFiber70StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 31) []
    (chainClosureStep tmWord tmFiber70Prefix30 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 15) hparentBefore tmFiber70ReverseSingleStep31

theorem tmFiber70State31_in_pass1_full :
    tmFiber70StateAt 31 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix31 ++ [tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix31 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 31) tmFiber70State31_in_pass1_prefix31

theorem tmFiber70State34_in_pass1_prefix34 :
    tmFiber70StateAt 34 ∈ chainClosureStep tmWord tmFiber70Prefix34 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 20 ∈
      chainClosureStep tmWord tmFiber70Prefix33 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix33 = tmFiber70Prefix20 ++ [tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33]
      (chainClosureStep tmWord tmFiber70Prefix20 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 20) tmFiber70State20_in_pass1_prefix20
  rw [show tmFiber70Prefix34 = tmFiber70Prefix33 ++ [tmFiber70StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 34) []
    (chainClosureStep tmWord tmFiber70Prefix33 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 20) hparentBefore tmFiber70ReverseSingleStep34

theorem tmFiber70State34_in_pass1_full :
    tmFiber70StateAt 34 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix34 ++ [tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix34 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 34) tmFiber70State34_in_pass1_prefix34

theorem tmFiber70State35_in_pass1_prefix35 :
    tmFiber70StateAt 35 ∈ chainClosureStep tmWord tmFiber70Prefix35 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 21 ∈
      chainClosureStep tmWord tmFiber70Prefix34 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix34 = tmFiber70Prefix21 ++ [tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34]
      (chainClosureStep tmWord tmFiber70Prefix21 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 21) tmFiber70State21_in_pass1_prefix21
  rw [show tmFiber70Prefix35 = tmFiber70Prefix34 ++ [tmFiber70StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 35) []
    (chainClosureStep tmWord tmFiber70Prefix34 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 21) hparentBefore tmFiber70ReverseSingleStep35

theorem tmFiber70State35_in_pass1_full :
    tmFiber70StateAt 35 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix35 ++ [tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix35 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 35) tmFiber70State35_in_pass1_prefix35

theorem tmFiber70State36_in_pass1_prefix36 :
    tmFiber70StateAt 36 ∈ chainClosureStep tmWord tmFiber70Prefix36 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 16 ∈
      chainClosureStep tmWord tmFiber70Prefix35 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix35 = tmFiber70Prefix16 ++ [tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35]
      (chainClosureStep tmWord tmFiber70Prefix16 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 16) tmFiber70State16_in_pass1_prefix16
  rw [show tmFiber70Prefix36 = tmFiber70Prefix35 ++ [tmFiber70StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 36) []
    (chainClosureStep tmWord tmFiber70Prefix35 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 16) hparentBefore tmFiber70ReverseSingleStep36

theorem tmFiber70State36_in_pass1_full :
    tmFiber70StateAt 36 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix36 ++ [tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix36 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 36) tmFiber70State36_in_pass1_prefix36

theorem tmFiber70State37_in_pass1_prefix37 :
    tmFiber70StateAt 37 ∈ chainClosureStep tmWord tmFiber70Prefix37 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 17 ∈
      chainClosureStep tmWord tmFiber70Prefix36 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix36 = tmFiber70Prefix17 ++ [tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36]
      (chainClosureStep tmWord tmFiber70Prefix17 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 17) tmFiber70State17_in_pass1_prefix17
  rw [show tmFiber70Prefix37 = tmFiber70Prefix36 ++ [tmFiber70StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 37) []
    (chainClosureStep tmWord tmFiber70Prefix36 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 17) hparentBefore tmFiber70ReverseSingleStep37

theorem tmFiber70State37_in_pass1_full :
    tmFiber70StateAt 37 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix37 ++ [tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix37 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 37) tmFiber70State37_in_pass1_prefix37

theorem tmFiber70State38_in_pass1_prefix38 :
    tmFiber70StateAt 38 ∈ chainClosureStep tmWord tmFiber70Prefix38 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 18 ∈
      chainClosureStep tmWord tmFiber70Prefix37 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix37 = tmFiber70Prefix18 ++ [tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37]
      (chainClosureStep tmWord tmFiber70Prefix18 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 18) tmFiber70State18_in_pass1_prefix18
  rw [show tmFiber70Prefix38 = tmFiber70Prefix37 ++ [tmFiber70StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 38) []
    (chainClosureStep tmWord tmFiber70Prefix37 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 18) hparentBefore tmFiber70ReverseSingleStep38

theorem tmFiber70State38_in_pass1_full :
    tmFiber70StateAt 38 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix38 ++ [tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix38 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 38) tmFiber70State38_in_pass1_prefix38

theorem tmFiber70State39_in_pass1_prefix39 :
    tmFiber70StateAt 39 ∈ chainClosureStep tmWord tmFiber70Prefix39 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 19 ∈
      chainClosureStep tmWord tmFiber70Prefix38 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix38 = tmFiber70Prefix19 ++ [tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38]
      (chainClosureStep tmWord tmFiber70Prefix19 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 19) tmFiber70State19_in_pass1_prefix19
  rw [show tmFiber70Prefix39 = tmFiber70Prefix38 ++ [tmFiber70StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 39) []
    (chainClosureStep tmWord tmFiber70Prefix38 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 19) hparentBefore tmFiber70ReverseSingleStep39

theorem tmFiber70State39_in_pass1_full :
    tmFiber70StateAt 39 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix39 ++ [tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix39 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 39) tmFiber70State39_in_pass1_prefix39

theorem tmFiber70State50_in_pass1_prefix50 :
    tmFiber70StateAt 50 ∈ chainClosureStep tmWord tmFiber70Prefix50 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 12 ∈
      chainClosureStep tmWord tmFiber70Prefix49 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix49 = tmFiber70Prefix12 ++ [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49]
      (chainClosureStep tmWord tmFiber70Prefix12 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 12) tmFiber70State12_in_pass1_prefix12
  rw [show tmFiber70Prefix50 = tmFiber70Prefix49 ++ [tmFiber70StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 50) []
    (chainClosureStep tmWord tmFiber70Prefix49 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 12) hparentBefore tmFiber70ReverseSingleStep50

theorem tmFiber70State50_in_pass1_full :
    tmFiber70StateAt 50 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix50 ++ [tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix50 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 50) tmFiber70State50_in_pass1_prefix50

theorem tmFiber70State51_in_pass1_prefix51 :
    tmFiber70StateAt 51 ∈ chainClosureStep tmWord tmFiber70Prefix51 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 13 ∈
      chainClosureStep tmWord tmFiber70Prefix50 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix50 = tmFiber70Prefix13 ++ [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50]
      (chainClosureStep tmWord tmFiber70Prefix13 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 13) tmFiber70State13_in_pass1_prefix13
  rw [show tmFiber70Prefix51 = tmFiber70Prefix50 ++ [tmFiber70StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 51) []
    (chainClosureStep tmWord tmFiber70Prefix50 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 13) hparentBefore tmFiber70ReverseSingleStep51

theorem tmFiber70State51_in_pass1_full :
    tmFiber70StateAt 51 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix51 ++ [tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix51 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 51) tmFiber70State51_in_pass1_prefix51

theorem tmFiber70State52_in_pass1_prefix52 :
    tmFiber70StateAt 52 ∈ chainClosureStep tmWord tmFiber70Prefix52 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 8 ∈
      chainClosureStep tmWord tmFiber70Prefix51 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix51 = tmFiber70Prefix8 ++ [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51]
      (chainClosureStep tmWord tmFiber70Prefix8 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 8) tmFiber70State8_in_pass1_prefix8
  rw [show tmFiber70Prefix52 = tmFiber70Prefix51 ++ [tmFiber70StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 52) []
    (chainClosureStep tmWord tmFiber70Prefix51 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 8) hparentBefore tmFiber70ReverseSingleStep52

theorem tmFiber70State52_in_pass1_full :
    tmFiber70StateAt 52 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix52 ++ [tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix52 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 52) tmFiber70State52_in_pass1_prefix52

theorem tmFiber70State53_in_pass1_prefix53 :
    tmFiber70StateAt 53 ∈ chainClosureStep tmWord tmFiber70Prefix53 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 9 ∈
      chainClosureStep tmWord tmFiber70Prefix52 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix52 = tmFiber70Prefix9 ++ [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52]
      (chainClosureStep tmWord tmFiber70Prefix9 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 9) tmFiber70State9_in_pass1_prefix9
  rw [show tmFiber70Prefix53 = tmFiber70Prefix52 ++ [tmFiber70StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 53) []
    (chainClosureStep tmWord tmFiber70Prefix52 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 9) hparentBefore tmFiber70ReverseSingleStep53

theorem tmFiber70State53_in_pass1_full :
    tmFiber70StateAt 53 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix53 ++ [tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix53 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 53) tmFiber70State53_in_pass1_prefix53

theorem tmFiber70State54_in_pass1_prefix54 :
    tmFiber70StateAt 54 ∈ chainClosureStep tmWord tmFiber70Prefix54 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 10 ∈
      chainClosureStep tmWord tmFiber70Prefix53 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix53 = tmFiber70Prefix10 ++ [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53]
      (chainClosureStep tmWord tmFiber70Prefix10 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 10) tmFiber70State10_in_pass1_prefix10
  rw [show tmFiber70Prefix54 = tmFiber70Prefix53 ++ [tmFiber70StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 54) []
    (chainClosureStep tmWord tmFiber70Prefix53 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 10) hparentBefore tmFiber70ReverseSingleStep54

theorem tmFiber70State54_in_pass1_full :
    tmFiber70StateAt 54 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix54 ++ [tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix54 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 54) tmFiber70State54_in_pass1_prefix54

theorem tmFiber70State55_in_pass1_prefix55 :
    tmFiber70StateAt 55 ∈ chainClosureStep tmWord tmFiber70Prefix55 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 11 ∈
      chainClosureStep tmWord tmFiber70Prefix54 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix54 = tmFiber70Prefix11 ++ [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54]
      (chainClosureStep tmWord tmFiber70Prefix11 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 11) tmFiber70State11_in_pass1_prefix11
  rw [show tmFiber70Prefix55 = tmFiber70Prefix54 ++ [tmFiber70StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 55) []
    (chainClosureStep tmWord tmFiber70Prefix54 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 11) hparentBefore tmFiber70ReverseSingleStep55

theorem tmFiber70State55_in_pass1_full :
    tmFiber70StateAt 55 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix55 ++ [tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix55 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 55) tmFiber70State55_in_pass1_prefix55

theorem tmFiber70State58_in_pass1_prefix58 :
    tmFiber70StateAt 58 ∈ chainClosureStep tmWord tmFiber70Prefix58 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 4 ∈
      chainClosureStep tmWord tmFiber70Prefix57 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix57 = tmFiber70Prefix4 ++ [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57]
      (chainClosureStep tmWord tmFiber70Prefix4 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 4) tmFiber70State4_in_pass1_prefix4
  rw [show tmFiber70Prefix58 = tmFiber70Prefix57 ++ [tmFiber70StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 58) []
    (chainClosureStep tmWord tmFiber70Prefix57 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 4) hparentBefore tmFiber70ReverseSingleStep58

theorem tmFiber70State58_in_pass1_full :
    tmFiber70StateAt 58 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix58 ++ [tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix58 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 58) tmFiber70State58_in_pass1_prefix58

theorem tmFiber70State59_in_pass1_prefix59 :
    tmFiber70StateAt 59 ∈ chainClosureStep tmWord tmFiber70Prefix59 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 5 ∈
      chainClosureStep tmWord tmFiber70Prefix58 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix58 = tmFiber70Prefix5 ++ [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58]
      (chainClosureStep tmWord tmFiber70Prefix5 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 5) tmFiber70State5_in_pass1_prefix5
  rw [show tmFiber70Prefix59 = tmFiber70Prefix58 ++ [tmFiber70StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 59) []
    (chainClosureStep tmWord tmFiber70Prefix58 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 5) hparentBefore tmFiber70ReverseSingleStep59

theorem tmFiber70State59_in_pass1_full :
    tmFiber70StateAt 59 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix59 ++ [tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix59 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 59) tmFiber70State59_in_pass1_prefix59

theorem tmFiber70State60_in_pass1_prefix60 :
    tmFiber70StateAt 60 ∈ chainClosureStep tmWord tmFiber70Prefix60 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70Prefix59 ([tmFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix59
      ([tmFiber70StateAt 0]) (tmFiber70StateAt 0) (by simp)
  rw [show tmFiber70Prefix60 = tmFiber70Prefix59 ++ [tmFiber70StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 60) []
    (chainClosureStep tmWord tmFiber70Prefix59 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 0) hparentBefore tmFiber70ReverseSingleStep60

theorem tmFiber70State60_in_pass1_full :
    tmFiber70StateAt 60 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix60 ++ [tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix60 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 60) tmFiber70State60_in_pass1_prefix60

theorem tmFiber70State61_in_pass1_prefix61 :
    tmFiber70StateAt 61 ∈ chainClosureStep tmWord tmFiber70Prefix61 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70Prefix60 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix60 = tmFiber70Prefix1 ++ [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 2, tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60]
      (chainClosureStep tmWord tmFiber70Prefix1 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 1) tmFiber70State1_in_pass1_prefix1
  rw [show tmFiber70Prefix61 = tmFiber70Prefix60 ++ [tmFiber70StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 61) []
    (chainClosureStep tmWord tmFiber70Prefix60 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 1) hparentBefore tmFiber70ReverseSingleStep61

theorem tmFiber70State61_in_pass1_full :
    tmFiber70StateAt 61 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix61 ++ [tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix61 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 61) tmFiber70State61_in_pass1_prefix61

theorem tmFiber70State62_in_pass1_prefix62 :
    tmFiber70StateAt 62 ∈ chainClosureStep tmWord tmFiber70Prefix62 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 2 ∈
      chainClosureStep tmWord tmFiber70Prefix61 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix61 = tmFiber70Prefix2 ++ [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 3, tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61]
      (chainClosureStep tmWord tmFiber70Prefix2 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 2) tmFiber70State2_in_pass1_prefix2
  rw [show tmFiber70Prefix62 = tmFiber70Prefix61 ++ [tmFiber70StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 62) []
    (chainClosureStep tmWord tmFiber70Prefix61 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 2) hparentBefore tmFiber70ReverseSingleStep62

theorem tmFiber70State62_in_pass1_full :
    tmFiber70StateAt 62 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix62 ++ [tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix62 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 62) tmFiber70State62_in_pass1_prefix62

theorem tmFiber70State63_in_pass1_prefix63 :
    tmFiber70StateAt 63 ∈ chainClosureStep tmWord tmFiber70Prefix63 ([tmFiber70StateAt 0]) := by
  have hparentBefore : tmFiber70StateAt 3 ∈
      chainClosureStep tmWord tmFiber70Prefix62 ([tmFiber70StateAt 0]) := by
    rw [show tmFiber70Prefix62 = tmFiber70Prefix3 ++ [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 4, tmFiber70StateAt 5, tmFiber70StateAt 6, tmFiber70StateAt 7, tmFiber70StateAt 8, tmFiber70StateAt 9, tmFiber70StateAt 10, tmFiber70StateAt 11, tmFiber70StateAt 12, tmFiber70StateAt 13, tmFiber70StateAt 14, tmFiber70StateAt 15, tmFiber70StateAt 16, tmFiber70StateAt 17, tmFiber70StateAt 18, tmFiber70StateAt 19, tmFiber70StateAt 20, tmFiber70StateAt 21, tmFiber70StateAt 22, tmFiber70StateAt 23, tmFiber70StateAt 24, tmFiber70StateAt 25, tmFiber70StateAt 26, tmFiber70StateAt 27, tmFiber70StateAt 28, tmFiber70StateAt 29, tmFiber70StateAt 30, tmFiber70StateAt 31, tmFiber70StateAt 32, tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62]
      (chainClosureStep tmWord tmFiber70Prefix3 ([tmFiber70StateAt 0]))
      (tmFiber70StateAt 3) tmFiber70State3_in_pass1_prefix3
  rw [show tmFiber70Prefix63 = tmFiber70Prefix62 ++ [tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 63) []
    (chainClosureStep tmWord tmFiber70Prefix62 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 3) hparentBefore tmFiber70ReverseSingleStep63

theorem tmFiber70State63_in_pass1_full :
    tmFiber70StateAt 63 ∈ chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord []
    (chainClosureStep tmWord tmFiber70Prefix63 ([tmFiber70StateAt 0]))
    (tmFiber70StateAt 63) tmFiber70State63_in_pass1_prefix63

theorem tmFiber70State32_in_pass2_prefix32 :
    tmFiber70StateAt 32 ∈ chainClosureStep tmWord tmFiber70Prefix32 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 36 ∈
      chainClosureStep tmWord tmFiber70Prefix31 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix31
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 36) tmFiber70State36_in_pass1_full
  rw [show tmFiber70Prefix32 = tmFiber70Prefix31 ++ [tmFiber70StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 32) []
    (chainClosureStep tmWord tmFiber70Prefix31 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 36) hparentBefore tmFiber70ReverseSingleStep32

theorem tmFiber70State32_in_pass2_full :
    tmFiber70StateAt 32 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix32 ++ [tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 33, tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix32 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 32) tmFiber70State32_in_pass2_prefix32

theorem tmFiber70State33_in_pass2_prefix33 :
    tmFiber70StateAt 33 ∈ chainClosureStep tmWord tmFiber70Prefix33 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 37 ∈
      chainClosureStep tmWord tmFiber70Prefix32 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix32
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 37) tmFiber70State37_in_pass1_full
  rw [show tmFiber70Prefix33 = tmFiber70Prefix32 ++ [tmFiber70StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 33) []
    (chainClosureStep tmWord tmFiber70Prefix32 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 37) hparentBefore tmFiber70ReverseSingleStep33

theorem tmFiber70State33_in_pass2_full :
    tmFiber70StateAt 33 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix33 ++ [tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 34, tmFiber70StateAt 35, tmFiber70StateAt 36, tmFiber70StateAt 37, tmFiber70StateAt 38, tmFiber70StateAt 39, tmFiber70StateAt 40, tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix33 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 33) tmFiber70State33_in_pass2_prefix33

theorem tmFiber70State42_in_pass2_prefix42 :
    tmFiber70StateAt 42 ∈ chainClosureStep tmWord tmFiber70Prefix42 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 58 ∈
      chainClosureStep tmWord tmFiber70Prefix41 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix41
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 58) tmFiber70State58_in_pass1_full
  rw [show tmFiber70Prefix42 = tmFiber70Prefix41 ++ [tmFiber70StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 42) []
    (chainClosureStep tmWord tmFiber70Prefix41 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 58) hparentBefore tmFiber70ReverseSingleStep42

theorem tmFiber70State42_in_pass2_full :
    tmFiber70StateAt 42 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix42 ++ [tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix42 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 42) tmFiber70State42_in_pass2_prefix42

theorem tmFiber70State43_in_pass2_prefix43 :
    tmFiber70StateAt 43 ∈ chainClosureStep tmWord tmFiber70Prefix43 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 59 ∈
      chainClosureStep tmWord tmFiber70Prefix42 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix42
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 59) tmFiber70State59_in_pass1_full
  rw [show tmFiber70Prefix43 = tmFiber70Prefix42 ++ [tmFiber70StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 43) []
    (chainClosureStep tmWord tmFiber70Prefix42 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 59) hparentBefore tmFiber70ReverseSingleStep43

theorem tmFiber70State43_in_pass2_full :
    tmFiber70StateAt 43 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix43 ++ [tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix43 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 43) tmFiber70State43_in_pass2_prefix43

theorem tmFiber70State44_in_pass2_prefix44 :
    tmFiber70StateAt 44 ∈ chainClosureStep tmWord tmFiber70Prefix44 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 60 ∈
      chainClosureStep tmWord tmFiber70Prefix43 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix43
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 60) tmFiber70State60_in_pass1_full
  rw [show tmFiber70Prefix44 = tmFiber70Prefix43 ++ [tmFiber70StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 44) []
    (chainClosureStep tmWord tmFiber70Prefix43 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 60) hparentBefore tmFiber70ReverseSingleStep44

theorem tmFiber70State44_in_pass2_full :
    tmFiber70StateAt 44 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix44 ++ [tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix44 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 44) tmFiber70State44_in_pass2_prefix44

theorem tmFiber70State45_in_pass2_prefix45 :
    tmFiber70StateAt 45 ∈ chainClosureStep tmWord tmFiber70Prefix45 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 61 ∈
      chainClosureStep tmWord tmFiber70Prefix44 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix44
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 61) tmFiber70State61_in_pass1_full
  rw [show tmFiber70Prefix45 = tmFiber70Prefix44 ++ [tmFiber70StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 45) []
    (chainClosureStep tmWord tmFiber70Prefix44 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 61) hparentBefore tmFiber70ReverseSingleStep45

theorem tmFiber70State45_in_pass2_full :
    tmFiber70StateAt 45 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix45 ++ [tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix45 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 45) tmFiber70State45_in_pass2_prefix45

theorem tmFiber70State46_in_pass2_prefix46 :
    tmFiber70StateAt 46 ∈ chainClosureStep tmWord tmFiber70Prefix46 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 62 ∈
      chainClosureStep tmWord tmFiber70Prefix45 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix45
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 62) tmFiber70State62_in_pass1_full
  rw [show tmFiber70Prefix46 = tmFiber70Prefix45 ++ [tmFiber70StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 46) []
    (chainClosureStep tmWord tmFiber70Prefix45 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 62) hparentBefore tmFiber70ReverseSingleStep46

theorem tmFiber70State46_in_pass2_full :
    tmFiber70StateAt 46 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix46 ++ [tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix46 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 46) tmFiber70State46_in_pass2_prefix46

theorem tmFiber70State47_in_pass2_prefix47 :
    tmFiber70StateAt 47 ∈ chainClosureStep tmWord tmFiber70Prefix47 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 63 ∈
      chainClosureStep tmWord tmFiber70Prefix46 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix46
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 63) tmFiber70State63_in_pass1_full
  rw [show tmFiber70Prefix47 = tmFiber70Prefix46 ++ [tmFiber70StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 47) []
    (chainClosureStep tmWord tmFiber70Prefix46 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 63) hparentBefore tmFiber70ReverseSingleStep47

theorem tmFiber70State47_in_pass2_full :
    tmFiber70StateAt 47 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix47 ++ [tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix47 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 47) tmFiber70State47_in_pass2_prefix47

theorem tmFiber70State48_in_pass2_prefix48 :
    tmFiber70StateAt 48 ∈ chainClosureStep tmWord tmFiber70Prefix48 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 52 ∈
      chainClosureStep tmWord tmFiber70Prefix47 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix47
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 52) tmFiber70State52_in_pass1_full
  rw [show tmFiber70Prefix48 = tmFiber70Prefix47 ++ [tmFiber70StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 48) []
    (chainClosureStep tmWord tmFiber70Prefix47 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 52) hparentBefore tmFiber70ReverseSingleStep48

theorem tmFiber70State48_in_pass2_full :
    tmFiber70StateAt 48 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix48 ++ [tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix48 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 48) tmFiber70State48_in_pass2_prefix48

theorem tmFiber70State49_in_pass2_prefix49 :
    tmFiber70StateAt 49 ∈ chainClosureStep tmWord tmFiber70Prefix49 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 53 ∈
      chainClosureStep tmWord tmFiber70Prefix48 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix48
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 53) tmFiber70State53_in_pass1_full
  rw [show tmFiber70Prefix49 = tmFiber70Prefix48 ++ [tmFiber70StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 49) []
    (chainClosureStep tmWord tmFiber70Prefix48 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 53) hparentBefore tmFiber70ReverseSingleStep49

theorem tmFiber70State49_in_pass2_full :
    tmFiber70StateAt 49 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix49 ++ [tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix49 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 49) tmFiber70State49_in_pass2_prefix49

theorem tmFiber70State56_in_pass2_prefix56 :
    tmFiber70StateAt 56 ∈ chainClosureStep tmWord tmFiber70Prefix56 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 60 ∈
      chainClosureStep tmWord tmFiber70Prefix55 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix55
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 60) tmFiber70State60_in_pass1_full
  rw [show tmFiber70Prefix56 = tmFiber70Prefix55 ++ [tmFiber70StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 56) []
    (chainClosureStep tmWord tmFiber70Prefix55 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 60) hparentBefore tmFiber70ReverseSingleStep56

theorem tmFiber70State56_in_pass2_full :
    tmFiber70StateAt 56 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix56 ++ [tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix56 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 56) tmFiber70State56_in_pass2_prefix56

theorem tmFiber70State57_in_pass2_prefix57 :
    tmFiber70StateAt 57 ∈ chainClosureStep tmWord tmFiber70Prefix57 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  have hparentBefore : tmFiber70StateAt 61 ∈
      chainClosureStep tmWord tmFiber70Prefix56 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix56
      (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) (tmFiber70StateAt 61) tmFiber70State61_in_pass1_full
  rw [show tmFiber70Prefix57 = tmFiber70Prefix56 ++ [tmFiber70StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 57) []
    (chainClosureStep tmWord tmFiber70Prefix56 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 61) hparentBefore tmFiber70ReverseSingleStep57

theorem tmFiber70State57_in_pass2_full :
    tmFiber70StateAt 57 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix57 ++ [tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix57 (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0])))
    (tmFiber70StateAt 57) tmFiber70State57_in_pass2_prefix57

theorem tmFiber70State40_in_pass3_prefix40 :
    tmFiber70StateAt 40 ∈ chainClosureStep tmWord tmFiber70Prefix40 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
  have hparentBefore : tmFiber70StateAt 44 ∈
      chainClosureStep tmWord tmFiber70Prefix39 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix39
      (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) (tmFiber70StateAt 44) tmFiber70State44_in_pass2_full
  rw [show tmFiber70Prefix40 = tmFiber70Prefix39 ++ [tmFiber70StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 40) []
    (chainClosureStep tmWord tmFiber70Prefix39 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))))
    (tmFiber70StateAt 44) hparentBefore tmFiber70ReverseSingleStep40

theorem tmFiber70State40_in_pass3_full :
    tmFiber70StateAt 40 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix40 ++ [tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 41, tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix40 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))))
    (tmFiber70StateAt 40) tmFiber70State40_in_pass3_prefix40

theorem tmFiber70State41_in_pass3_prefix41 :
    tmFiber70StateAt 41 ∈ chainClosureStep tmWord tmFiber70Prefix41 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
  have hparentBefore : tmFiber70StateAt 45 ∈
      chainClosureStep tmWord tmFiber70Prefix40 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
    exact chainClosureStep_mem_of_seen tmWord tmFiber70Prefix40
      (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) (tmFiber70StateAt 45) tmFiber70State45_in_pass2_full
  rw [show tmFiber70Prefix41 = tmFiber70Prefix40 ++ [tmFiber70StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step tmWord (tmFiber70StateAt 41) []
    (chainClosureStep tmWord tmFiber70Prefix40 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))))
    (tmFiber70StateAt 45) hparentBefore tmFiber70ReverseSingleStep41

theorem tmFiber70State41_in_pass3_full :
    tmFiber70StateAt 41 ∈ chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))) := by
  rw [show tmFiber70DirectStates = tmFiber70Prefix41 ++ [tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen tmWord [tmFiber70StateAt 42, tmFiber70StateAt 43, tmFiber70StateAt 44, tmFiber70StateAt 45, tmFiber70StateAt 46, tmFiber70StateAt 47, tmFiber70StateAt 48, tmFiber70StateAt 49, tmFiber70StateAt 50, tmFiber70StateAt 51, tmFiber70StateAt 52, tmFiber70StateAt 53, tmFiber70StateAt 54, tmFiber70StateAt 55, tmFiber70StateAt 56, tmFiber70StateAt 57, tmFiber70StateAt 58, tmFiber70StateAt 59, tmFiber70StateAt 60, tmFiber70StateAt 61, tmFiber70StateAt 62, tmFiber70StateAt 63]
    (chainClosureStep tmWord tmFiber70Prefix41 (chainClosureStep tmWord tmFiber70DirectStates (chainClosureStep tmWord tmFiber70DirectStates ([tmFiber70StateAt 0]))))
    (tmFiber70StateAt 41) tmFiber70State41_in_pass3_prefix41

theorem tmFiber70FirstPassGrows :
    ((chainClosureStep tmWord tmFiber70DirectStates [tmFiber70StateAt 0]).length ==
      [tmFiber70StateAt 0].length) = false := by
  have hroot : tmFiber70StateAt 0 ∈
      chainClosureStep tmWord tmFiber70DirectStates [tmFiber70StateAt 0] :=
    chainClosureStep_mem_of_seen tmWord tmFiber70DirectStates
      [tmFiber70StateAt 0] (tmFiber70StateAt 0) (by simp)
  have hnew : tmFiber70StateAt 1 ∈
      chainClosureStep tmWord tmFiber70DirectStates [tmFiber70StateAt 0] :=
    tmFiber70State1_in_pass1_full
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep tmWord tmFiber70DirectStates [tmFiber70StateAt 0])
    (tmFiber70StateAt 0) (tmFiber70StateAt 1) hroot hnew (by decide)

theorem tmFiber70State0_in_close_short :
    tmFiber70StateAt 0 ∈ closeChainFiber tmWord tmFiber70DirectStates 0 [tmFiber70StateAt 0] := by
  simp [closeChainFiber]

theorem tmFiber70State1_in_close_short :
    tmFiber70StateAt 1 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 1) tmFiber70State1_in_pass1_full

theorem tmFiber70State2_in_close_short :
    tmFiber70StateAt 2 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 2) tmFiber70State2_in_pass1_full

theorem tmFiber70State3_in_close_short :
    tmFiber70StateAt 3 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 3) tmFiber70State3_in_pass1_full

theorem tmFiber70State4_in_close_short :
    tmFiber70StateAt 4 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 4) tmFiber70State4_in_pass1_full

theorem tmFiber70State5_in_close_short :
    tmFiber70StateAt 5 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 5) tmFiber70State5_in_pass1_full

theorem tmFiber70State6_in_close_short :
    tmFiber70StateAt 6 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 6) tmFiber70State6_in_pass1_full

theorem tmFiber70State7_in_close_short :
    tmFiber70StateAt 7 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 7) tmFiber70State7_in_pass1_full

theorem tmFiber70State8_in_close_short :
    tmFiber70StateAt 8 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 8) tmFiber70State8_in_pass1_full

theorem tmFiber70State9_in_close_short :
    tmFiber70StateAt 9 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 9) tmFiber70State9_in_pass1_full

theorem tmFiber70State10_in_close_short :
    tmFiber70StateAt 10 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 10) tmFiber70State10_in_pass1_full

theorem tmFiber70State11_in_close_short :
    tmFiber70StateAt 11 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 11) tmFiber70State11_in_pass1_full

theorem tmFiber70State12_in_close_short :
    tmFiber70StateAt 12 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 12) tmFiber70State12_in_pass1_full

theorem tmFiber70State13_in_close_short :
    tmFiber70StateAt 13 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 13) tmFiber70State13_in_pass1_full

theorem tmFiber70State14_in_close_short :
    tmFiber70StateAt 14 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 14) tmFiber70State14_in_pass1_full

theorem tmFiber70State15_in_close_short :
    tmFiber70StateAt 15 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 15) tmFiber70State15_in_pass1_full

theorem tmFiber70State16_in_close_short :
    tmFiber70StateAt 16 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 16) tmFiber70State16_in_pass1_full

theorem tmFiber70State17_in_close_short :
    tmFiber70StateAt 17 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 17) tmFiber70State17_in_pass1_full

theorem tmFiber70State18_in_close_short :
    tmFiber70StateAt 18 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 18) tmFiber70State18_in_pass1_full

theorem tmFiber70State19_in_close_short :
    tmFiber70StateAt 19 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 19) tmFiber70State19_in_pass1_full

theorem tmFiber70State20_in_close_short :
    tmFiber70StateAt 20 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 20) tmFiber70State20_in_pass1_full

theorem tmFiber70State21_in_close_short :
    tmFiber70StateAt 21 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 21) tmFiber70State21_in_pass1_full

theorem tmFiber70State22_in_close_short :
    tmFiber70StateAt 22 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 22) tmFiber70State22_in_pass1_full

theorem tmFiber70State23_in_close_short :
    tmFiber70StateAt 23 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 23) tmFiber70State23_in_pass1_full

theorem tmFiber70State24_in_close_short :
    tmFiber70StateAt 24 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 24) tmFiber70State24_in_pass1_full

theorem tmFiber70State25_in_close_short :
    tmFiber70StateAt 25 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 25) tmFiber70State25_in_pass1_full

theorem tmFiber70State26_in_close_short :
    tmFiber70StateAt 26 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 26) tmFiber70State26_in_pass1_full

theorem tmFiber70State27_in_close_short :
    tmFiber70StateAt 27 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 27) tmFiber70State27_in_pass1_full

theorem tmFiber70State28_in_close_short :
    tmFiber70StateAt 28 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 28) tmFiber70State28_in_pass1_full

theorem tmFiber70State29_in_close_short :
    tmFiber70StateAt 29 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 29) tmFiber70State29_in_pass1_full

theorem tmFiber70State30_in_close_short :
    tmFiber70StateAt 30 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 30) tmFiber70State30_in_pass1_full

theorem tmFiber70State31_in_close_short :
    tmFiber70StateAt 31 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 31) tmFiber70State31_in_pass1_full

theorem tmFiber70State34_in_close_short :
    tmFiber70StateAt 34 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 34) tmFiber70State34_in_pass1_full

theorem tmFiber70State35_in_close_short :
    tmFiber70StateAt 35 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 35) tmFiber70State35_in_pass1_full

theorem tmFiber70State36_in_close_short :
    tmFiber70StateAt 36 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 36) tmFiber70State36_in_pass1_full

theorem tmFiber70State37_in_close_short :
    tmFiber70StateAt 37 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 37) tmFiber70State37_in_pass1_full

theorem tmFiber70State38_in_close_short :
    tmFiber70StateAt 38 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 38) tmFiber70State38_in_pass1_full

theorem tmFiber70State39_in_close_short :
    tmFiber70StateAt 39 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 39) tmFiber70State39_in_pass1_full

theorem tmFiber70State50_in_close_short :
    tmFiber70StateAt 50 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 50) tmFiber70State50_in_pass1_full

theorem tmFiber70State51_in_close_short :
    tmFiber70StateAt 51 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 51) tmFiber70State51_in_pass1_full

theorem tmFiber70State52_in_close_short :
    tmFiber70StateAt 52 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 52) tmFiber70State52_in_pass1_full

theorem tmFiber70State53_in_close_short :
    tmFiber70StateAt 53 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 53) tmFiber70State53_in_pass1_full

theorem tmFiber70State54_in_close_short :
    tmFiber70StateAt 54 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 54) tmFiber70State54_in_pass1_full

theorem tmFiber70State55_in_close_short :
    tmFiber70StateAt 55 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 55) tmFiber70State55_in_pass1_full

theorem tmFiber70State58_in_close_short :
    tmFiber70StateAt 58 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 58) tmFiber70State58_in_pass1_full

theorem tmFiber70State59_in_close_short :
    tmFiber70StateAt 59 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 59) tmFiber70State59_in_pass1_full

theorem tmFiber70State60_in_close_short :
    tmFiber70StateAt 60 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 60) tmFiber70State60_in_pass1_full

theorem tmFiber70State61_in_close_short :
    tmFiber70StateAt 61 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 61) tmFiber70State61_in_pass1_full

theorem tmFiber70State62_in_close_short :
    tmFiber70StateAt 62 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 62) tmFiber70State62_in_pass1_full

theorem tmFiber70State63_in_close_short :
    tmFiber70StateAt 63 ∈ closeChainFiber tmWord tmFiber70DirectStates 1 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 63) tmFiber70State63_in_pass1_full

theorem tmFiber70State32_in_close_short :
    tmFiber70StateAt 32 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 32) tmFiber70FirstPassGrows
    tmFiber70State32_in_pass2_full

theorem tmFiber70State33_in_close_short :
    tmFiber70StateAt 33 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 33) tmFiber70FirstPassGrows
    tmFiber70State33_in_pass2_full

theorem tmFiber70State42_in_close_short :
    tmFiber70StateAt 42 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 42) tmFiber70FirstPassGrows
    tmFiber70State42_in_pass2_full

theorem tmFiber70State43_in_close_short :
    tmFiber70StateAt 43 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 43) tmFiber70FirstPassGrows
    tmFiber70State43_in_pass2_full

theorem tmFiber70State44_in_close_short :
    tmFiber70StateAt 44 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 44) tmFiber70FirstPassGrows
    tmFiber70State44_in_pass2_full

theorem tmFiber70State45_in_close_short :
    tmFiber70StateAt 45 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 45) tmFiber70FirstPassGrows
    tmFiber70State45_in_pass2_full

theorem tmFiber70State46_in_close_short :
    tmFiber70StateAt 46 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 46) tmFiber70FirstPassGrows
    tmFiber70State46_in_pass2_full

theorem tmFiber70State47_in_close_short :
    tmFiber70StateAt 47 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 47) tmFiber70FirstPassGrows
    tmFiber70State47_in_pass2_full

theorem tmFiber70State48_in_close_short :
    tmFiber70StateAt 48 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 48) tmFiber70FirstPassGrows
    tmFiber70State48_in_pass2_full

theorem tmFiber70State49_in_close_short :
    tmFiber70StateAt 49 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 49) tmFiber70FirstPassGrows
    tmFiber70State49_in_pass2_full

theorem tmFiber70State56_in_close_short :
    tmFiber70StateAt 56 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 56) tmFiber70FirstPassGrows
    tmFiber70State56_in_pass2_full

theorem tmFiber70State57_in_close_short :
    tmFiber70StateAt 57 ∈ closeChainFiber tmWord tmFiber70DirectStates 2 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_second_closureStep tmWord tmFiber70DirectStates 0
    [tmFiber70StateAt 0] (tmFiber70StateAt 57) tmFiber70FirstPassGrows
    tmFiber70State57_in_pass2_full

theorem tmFiber70State40_in_close_short :
    tmFiber70StateAt 40 ∈ closeChainFiber tmWord tmFiber70DirectStates 3 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber70DirectStates 2
    [tmFiber70StateAt 0] (tmFiber70StateAt 44) (tmFiber70StateAt 40)
    (by simp) tmFiber70State44_in_close_short (by decide) tmFiber70ReverseSingleStep40

theorem tmFiber70State41_in_close_short :
    tmFiber70StateAt 41 ∈ closeChainFiber tmWord tmFiber70DirectStates 3 [tmFiber70StateAt 0] := by
  exact closeChainFiber_mem_step_of_close tmWord tmFiber70DirectStates 2
    [tmFiber70StateAt 0] (tmFiber70StateAt 45) (tmFiber70StateAt 41)
    (by simp) tmFiber70State45_in_close_short (by decide) tmFiber70ReverseSingleStep41

theorem tmFiber70State0_in_close :
    tmFiber70StateAt 0 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 0 ∈ closeChainFiber tmWord tmFiber70DirectStates (0 + 64) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 0 64
    [tmFiber70StateAt 0] (tmFiber70StateAt 0) tmFiber70State0_in_close_short

theorem tmFiber70State1_in_close :
    tmFiber70StateAt 1 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 1 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 1) tmFiber70State1_in_close_short

theorem tmFiber70State2_in_close :
    tmFiber70StateAt 2 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 2 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 2) tmFiber70State2_in_close_short

theorem tmFiber70State3_in_close :
    tmFiber70StateAt 3 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 3 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 3) tmFiber70State3_in_close_short

theorem tmFiber70State4_in_close :
    tmFiber70StateAt 4 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 4 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 4) tmFiber70State4_in_close_short

theorem tmFiber70State5_in_close :
    tmFiber70StateAt 5 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 5 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 5) tmFiber70State5_in_close_short

theorem tmFiber70State6_in_close :
    tmFiber70StateAt 6 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 6 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 6) tmFiber70State6_in_close_short

theorem tmFiber70State7_in_close :
    tmFiber70StateAt 7 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 7 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 7) tmFiber70State7_in_close_short

theorem tmFiber70State8_in_close :
    tmFiber70StateAt 8 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 8 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 8) tmFiber70State8_in_close_short

theorem tmFiber70State9_in_close :
    tmFiber70StateAt 9 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 9 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 9) tmFiber70State9_in_close_short

theorem tmFiber70State10_in_close :
    tmFiber70StateAt 10 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 10 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 10) tmFiber70State10_in_close_short

theorem tmFiber70State11_in_close :
    tmFiber70StateAt 11 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 11 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 11) tmFiber70State11_in_close_short

theorem tmFiber70State12_in_close :
    tmFiber70StateAt 12 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 12 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 12) tmFiber70State12_in_close_short

theorem tmFiber70State13_in_close :
    tmFiber70StateAt 13 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 13 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 13) tmFiber70State13_in_close_short

theorem tmFiber70State14_in_close :
    tmFiber70StateAt 14 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 14 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 14) tmFiber70State14_in_close_short

theorem tmFiber70State15_in_close :
    tmFiber70StateAt 15 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 15 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 15) tmFiber70State15_in_close_short

theorem tmFiber70State16_in_close :
    tmFiber70StateAt 16 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 16 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 16) tmFiber70State16_in_close_short

theorem tmFiber70State17_in_close :
    tmFiber70StateAt 17 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 17 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 17) tmFiber70State17_in_close_short

theorem tmFiber70State18_in_close :
    tmFiber70StateAt 18 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 18 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 18) tmFiber70State18_in_close_short

theorem tmFiber70State19_in_close :
    tmFiber70StateAt 19 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 19 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 19) tmFiber70State19_in_close_short

theorem tmFiber70State20_in_close :
    tmFiber70StateAt 20 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 20 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 20) tmFiber70State20_in_close_short

theorem tmFiber70State21_in_close :
    tmFiber70StateAt 21 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 21 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 21) tmFiber70State21_in_close_short

theorem tmFiber70State22_in_close :
    tmFiber70StateAt 22 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 22 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 22) tmFiber70State22_in_close_short

theorem tmFiber70State23_in_close :
    tmFiber70StateAt 23 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 23 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 23) tmFiber70State23_in_close_short

theorem tmFiber70State24_in_close :
    tmFiber70StateAt 24 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 24 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 24) tmFiber70State24_in_close_short

theorem tmFiber70State25_in_close :
    tmFiber70StateAt 25 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 25 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 25) tmFiber70State25_in_close_short

theorem tmFiber70State26_in_close :
    tmFiber70StateAt 26 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 26 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 26) tmFiber70State26_in_close_short

theorem tmFiber70State27_in_close :
    tmFiber70StateAt 27 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 27 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 27) tmFiber70State27_in_close_short

theorem tmFiber70State28_in_close :
    tmFiber70StateAt 28 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 28 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 28) tmFiber70State28_in_close_short

theorem tmFiber70State29_in_close :
    tmFiber70StateAt 29 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 29 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 29) tmFiber70State29_in_close_short

theorem tmFiber70State30_in_close :
    tmFiber70StateAt 30 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 30 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 30) tmFiber70State30_in_close_short

theorem tmFiber70State31_in_close :
    tmFiber70StateAt 31 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 31 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 31) tmFiber70State31_in_close_short

theorem tmFiber70State32_in_close :
    tmFiber70StateAt 32 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 32 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 32) tmFiber70State32_in_close_short

theorem tmFiber70State33_in_close :
    tmFiber70StateAt 33 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 33 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 33) tmFiber70State33_in_close_short

theorem tmFiber70State34_in_close :
    tmFiber70StateAt 34 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 34 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 34) tmFiber70State34_in_close_short

theorem tmFiber70State35_in_close :
    tmFiber70StateAt 35 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 35 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 35) tmFiber70State35_in_close_short

theorem tmFiber70State36_in_close :
    tmFiber70StateAt 36 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 36 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 36) tmFiber70State36_in_close_short

theorem tmFiber70State37_in_close :
    tmFiber70StateAt 37 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 37 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 37) tmFiber70State37_in_close_short

theorem tmFiber70State38_in_close :
    tmFiber70StateAt 38 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 38 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 38) tmFiber70State38_in_close_short

theorem tmFiber70State39_in_close :
    tmFiber70StateAt 39 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 39 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 39) tmFiber70State39_in_close_short

theorem tmFiber70State40_in_close :
    tmFiber70StateAt 40 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 40 ∈ closeChainFiber tmWord tmFiber70DirectStates (3 + 61) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 3 61
    [tmFiber70StateAt 0] (tmFiber70StateAt 40) tmFiber70State40_in_close_short

theorem tmFiber70State41_in_close :
    tmFiber70StateAt 41 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 41 ∈ closeChainFiber tmWord tmFiber70DirectStates (3 + 61) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 3 61
    [tmFiber70StateAt 0] (tmFiber70StateAt 41) tmFiber70State41_in_close_short

theorem tmFiber70State42_in_close :
    tmFiber70StateAt 42 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 42 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 42) tmFiber70State42_in_close_short

theorem tmFiber70State43_in_close :
    tmFiber70StateAt 43 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 43 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 43) tmFiber70State43_in_close_short

theorem tmFiber70State44_in_close :
    tmFiber70StateAt 44 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 44 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 44) tmFiber70State44_in_close_short

theorem tmFiber70State45_in_close :
    tmFiber70StateAt 45 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 45 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 45) tmFiber70State45_in_close_short

theorem tmFiber70State46_in_close :
    tmFiber70StateAt 46 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 46 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 46) tmFiber70State46_in_close_short

theorem tmFiber70State47_in_close :
    tmFiber70StateAt 47 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 47 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 47) tmFiber70State47_in_close_short

theorem tmFiber70State48_in_close :
    tmFiber70StateAt 48 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 48 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 48) tmFiber70State48_in_close_short

theorem tmFiber70State49_in_close :
    tmFiber70StateAt 49 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 49 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 49) tmFiber70State49_in_close_short

theorem tmFiber70State50_in_close :
    tmFiber70StateAt 50 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 50 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 50) tmFiber70State50_in_close_short

theorem tmFiber70State51_in_close :
    tmFiber70StateAt 51 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 51 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 51) tmFiber70State51_in_close_short

theorem tmFiber70State52_in_close :
    tmFiber70StateAt 52 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 52 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 52) tmFiber70State52_in_close_short

theorem tmFiber70State53_in_close :
    tmFiber70StateAt 53 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 53 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 53) tmFiber70State53_in_close_short

theorem tmFiber70State54_in_close :
    tmFiber70StateAt 54 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 54 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 54) tmFiber70State54_in_close_short

theorem tmFiber70State55_in_close :
    tmFiber70StateAt 55 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 55 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 55) tmFiber70State55_in_close_short

theorem tmFiber70State56_in_close :
    tmFiber70StateAt 56 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 56 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 56) tmFiber70State56_in_close_short

theorem tmFiber70State57_in_close :
    tmFiber70StateAt 57 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 57 ∈ closeChainFiber tmWord tmFiber70DirectStates (2 + 62) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 2 62
    [tmFiber70StateAt 0] (tmFiber70StateAt 57) tmFiber70State57_in_close_short

theorem tmFiber70State58_in_close :
    tmFiber70StateAt 58 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 58 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 58) tmFiber70State58_in_close_short

theorem tmFiber70State59_in_close :
    tmFiber70StateAt 59 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 59 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 59) tmFiber70State59_in_close_short

theorem tmFiber70State60_in_close :
    tmFiber70StateAt 60 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 60 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 60) tmFiber70State60_in_close_short

theorem tmFiber70State61_in_close :
    tmFiber70StateAt 61 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 61 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 61) tmFiber70State61_in_close_short

theorem tmFiber70State62_in_close :
    tmFiber70StateAt 62 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 62 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 62) tmFiber70State62_in_close_short

theorem tmFiber70State63_in_close :
    tmFiber70StateAt 63 ∈ closeChainFiber tmWord tmFiber70DirectStates tmFiber70DirectStates.length [tmFiber70StateAt 0] := by
  change tmFiber70StateAt 63 ∈ closeChainFiber tmWord tmFiber70DirectStates (1 + 63) [tmFiber70StateAt 0]
  exact closeChainFiber_mem_mono_add tmWord tmFiber70DirectStates 1 63
    [tmFiber70StateAt 0] (tmFiber70StateAt 63) tmFiber70State63_in_close_short

theorem tmFiber70DirectConnected :
    chainFiberConnected tmWord tmFiber70DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [tmFiber70DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact tmFiber70State0_in_close
  · subst state
    exact tmFiber70State1_in_close
  · subst state
    exact tmFiber70State2_in_close
  · subst state
    exact tmFiber70State3_in_close
  · subst state
    exact tmFiber70State4_in_close
  · subst state
    exact tmFiber70State5_in_close
  · subst state
    exact tmFiber70State6_in_close
  · subst state
    exact tmFiber70State7_in_close
  · subst state
    exact tmFiber70State8_in_close
  · subst state
    exact tmFiber70State9_in_close
  · subst state
    exact tmFiber70State10_in_close
  · subst state
    exact tmFiber70State11_in_close
  · subst state
    exact tmFiber70State12_in_close
  · subst state
    exact tmFiber70State13_in_close
  · subst state
    exact tmFiber70State14_in_close
  · subst state
    exact tmFiber70State15_in_close
  · subst state
    exact tmFiber70State16_in_close
  · subst state
    exact tmFiber70State17_in_close
  · subst state
    exact tmFiber70State18_in_close
  · subst state
    exact tmFiber70State19_in_close
  · subst state
    exact tmFiber70State20_in_close
  · subst state
    exact tmFiber70State21_in_close
  · subst state
    exact tmFiber70State22_in_close
  · subst state
    exact tmFiber70State23_in_close
  · subst state
    exact tmFiber70State24_in_close
  · subst state
    exact tmFiber70State25_in_close
  · subst state
    exact tmFiber70State26_in_close
  · subst state
    exact tmFiber70State27_in_close
  · subst state
    exact tmFiber70State28_in_close
  · subst state
    exact tmFiber70State29_in_close
  · subst state
    exact tmFiber70State30_in_close
  · subst state
    exact tmFiber70State31_in_close
  · subst state
    exact tmFiber70State32_in_close
  · subst state
    exact tmFiber70State33_in_close
  · subst state
    exact tmFiber70State34_in_close
  · subst state
    exact tmFiber70State35_in_close
  · subst state
    exact tmFiber70State36_in_close
  · subst state
    exact tmFiber70State37_in_close
  · subst state
    exact tmFiber70State38_in_close
  · subst state
    exact tmFiber70State39_in_close
  · subst state
    exact tmFiber70State40_in_close
  · subst state
    exact tmFiber70State41_in_close
  · subst state
    exact tmFiber70State42_in_close
  · subst state
    exact tmFiber70State43_in_close
  · subst state
    exact tmFiber70State44_in_close
  · subst state
    exact tmFiber70State45_in_close
  · subst state
    exact tmFiber70State46_in_close
  · subst state
    exact tmFiber70State47_in_close
  · subst state
    exact tmFiber70State48_in_close
  · subst state
    exact tmFiber70State49_in_close
  · subst state
    exact tmFiber70State50_in_close
  · subst state
    exact tmFiber70State51_in_close
  · subst state
    exact tmFiber70State52_in_close
  · subst state
    exact tmFiber70State53_in_close
  · subst state
    exact tmFiber70State54_in_close
  · subst state
    exact tmFiber70State55_in_close
  · subst state
    exact tmFiber70State56_in_close
  · subst state
    exact tmFiber70State57_in_close
  · subst state
    exact tmFiber70State58_in_close
  · subst state
    exact tmFiber70State59_in_close
  · subst state
    exact tmFiber70State60_in_close
  · subst state
    exact tmFiber70State61_in_close
  · subst state
    exact tmFiber70State62_in_close
  · subst state
    exact tmFiber70State63_in_close
  · cases h

end GoertzelLemma818LengthTwoTMLargeFiberBridge

end Mettapedia.GraphTheory.FourColor
