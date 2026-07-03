import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype multi-pass direct closure bridge for one generated length-two fiber

This module checks the proof shape for a generated `tau,tau` fiber whose
parent order requires two closure scans.  It remains a local bridge
prototype, not the final real `chainLKRInAudit` theorem.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber4StateAt (i : Nat) : List TauState :=
  directStates (ttFiber4RowAt i).sourceLeft (ttFiber4RowAt i).sourceRight

def ttFiber4DirectStates : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]

def ttFiber4Prefix0 : List (List TauState) :=
  [ttFiber4StateAt 0]

def ttFiber4Prefix1 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1]

def ttFiber4Prefix2 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2]

def ttFiber4Prefix3 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3]

def ttFiber4Prefix4 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4]

def ttFiber4Prefix5 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5]

def ttFiber4Prefix6 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6]

def ttFiber4Prefix7 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7]

def ttFiber4Prefix8 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8]

def ttFiber4Prefix9 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9]

def ttFiber4Prefix10 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10]

def ttFiber4Prefix11 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11]

def ttFiber4Prefix12 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12]

def ttFiber4Prefix13 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13]

def ttFiber4Prefix14 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14]

def ttFiber4Prefix15 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15]

def ttFiber4Prefix16 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16]

def ttFiber4Prefix17 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17]

def ttFiber4Prefix18 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18]

def ttFiber4Prefix19 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19]

def ttFiber4Prefix20 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20]

def ttFiber4Prefix21 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21]

def ttFiber4Prefix22 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22]

def ttFiber4Prefix23 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23]

def ttFiber4Prefix24 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24]

def ttFiber4Prefix25 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25]

def ttFiber4Prefix26 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26]

def ttFiber4Prefix27 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27]

def ttFiber4Prefix28 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28]

def ttFiber4Prefix29 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29]

def ttFiber4Prefix30 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30]

def ttFiber4Prefix31 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31]

def ttFiber4Prefix32 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32]

def ttFiber4Prefix33 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33]

def ttFiber4Prefix34 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34]

def ttFiber4Prefix35 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35]

def ttFiber4Prefix36 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36]

def ttFiber4Prefix37 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37]

def ttFiber4Prefix38 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38]

def ttFiber4Prefix39 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39]

def ttFiber4Prefix40 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40]

def ttFiber4Prefix41 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41]

def ttFiber4Prefix42 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42]

def ttFiber4Prefix43 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43]

def ttFiber4Prefix44 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44]

def ttFiber4Prefix45 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45]

def ttFiber4Prefix46 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46]

def ttFiber4Prefix47 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47]

def ttFiber4Prefix48 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48]

def ttFiber4Prefix49 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49]

def ttFiber4Prefix50 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50]

def ttFiber4Prefix51 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51]

def ttFiber4Prefix52 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52]

def ttFiber4Prefix53 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53]

def ttFiber4Prefix54 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54]

def ttFiber4Prefix55 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55]

def ttFiber4Prefix56 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56]

def ttFiber4Prefix57 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57]

def ttFiber4Prefix58 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58]

def ttFiber4Prefix59 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59]

def ttFiber4Prefix60 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60]

def ttFiber4Prefix61 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61]

def ttFiber4Prefix62 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62]

def ttFiber4Prefix63 : List (List TauState) :=
  [ttFiber4StateAt 0, ttFiber4StateAt 1, ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]

theorem ttFiber4ReverseRow_1_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk0] at h
  exact h.2

theorem ttFiber4ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 1)
      (ttFiber4RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 1) (by decide) ttFiber4ReverseRow_1_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_2_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk1] at h
  exact h.1

theorem ttFiber4ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 2)
      (ttFiber4RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 2) (by decide) ttFiber4ReverseRow_2_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_3_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk1] at h
  exact h.2

theorem ttFiber4ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 3)
      (ttFiber4RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 3) (by decide) ttFiber4ReverseRow_3_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_4_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk2] at h
  exact h.1

theorem ttFiber4ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 4)
      (ttFiber4RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 4) (by decide) ttFiber4ReverseRow_4_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_5_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk2] at h
  exact h.2

theorem ttFiber4ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 5)
      (ttFiber4RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 5) (by decide) ttFiber4ReverseRow_5_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_6_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk3] at h
  exact h.1

theorem ttFiber4ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 6)
      (ttFiber4RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 6) (by decide) ttFiber4ReverseRow_6_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_7_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk3] at h
  exact h.2

theorem ttFiber4ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 7)
      (ttFiber4RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 7) (by decide) ttFiber4ReverseRow_7_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_8_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk4] at h
  exact h.1

theorem ttFiber4ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 8)
      (ttFiber4RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 8) (by decide) ttFiber4ReverseRow_8_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_9_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk4] at h
  exact h.2

theorem ttFiber4ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 9)
      (ttFiber4RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 9) (by decide) ttFiber4ReverseRow_9_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_10_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk5] at h
  exact h.1

theorem ttFiber4ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 10)
      (ttFiber4RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 10) (by decide) ttFiber4ReverseRow_10_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_11_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk5] at h
  exact h.2

theorem ttFiber4ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 11)
      (ttFiber4RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 11) (by decide) ttFiber4ReverseRow_11_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_12_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk6] at h
  exact h.1

theorem ttFiber4ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 4) (ttFiber4StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 4) (ttFiber4StateAt 12)
      (ttFiber4RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 12) (by decide) ttFiber4ReverseRow_12_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_13_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk6] at h
  exact h.2

theorem ttFiber4ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 5) (ttFiber4StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 5) (ttFiber4StateAt 13)
      (ttFiber4RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 13) (by decide) ttFiber4ReverseRow_13_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_14_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk7] at h
  exact h.1

theorem ttFiber4ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 14)
      (ttFiber4RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 14) (by decide) ttFiber4ReverseRow_14_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_15_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk7] at h
  exact h.2

theorem ttFiber4ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 15)
      (ttFiber4RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 15) (by decide) ttFiber4ReverseRow_15_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_16_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk8] at h
  exact h.1

theorem ttFiber4ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 16)
      (ttFiber4RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 16) (by decide) ttFiber4ReverseRow_16_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_17_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk8] at h
  exact h.2

theorem ttFiber4ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 17)
      (ttFiber4RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 17) (by decide) ttFiber4ReverseRow_17_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_18_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk9] at h
  exact h.1

theorem ttFiber4ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 18)
      (ttFiber4RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 18) (by decide) ttFiber4ReverseRow_18_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_19_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk9] at h
  exact h.2

theorem ttFiber4ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 19)
      (ttFiber4RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 19) (by decide) ttFiber4ReverseRow_19_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_20_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk10] at h
  exact h.1

theorem ttFiber4ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 16) (ttFiber4StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 16) (ttFiber4StateAt 20)
      (ttFiber4RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 20) (by decide) ttFiber4ReverseRow_20_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_21_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk10] at h
  exact h.2

theorem ttFiber4ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 17) (ttFiber4StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 17) (ttFiber4StateAt 21)
      (ttFiber4RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 21) (by decide) ttFiber4ReverseRow_21_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_22_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk11] at h
  exact h.1

theorem ttFiber4ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 22)
      (ttFiber4RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 22) (by decide) ttFiber4ReverseRow_22_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_23_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk11] at h
  exact h.2

theorem ttFiber4ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 23)
      (ttFiber4RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 23) (by decide) ttFiber4ReverseRow_23_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_24_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk12] at h
  exact h.1

theorem ttFiber4ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 8) (ttFiber4StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 8) (ttFiber4StateAt 24)
      (ttFiber4RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 24) (by decide) ttFiber4ReverseRow_24_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_25_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk12] at h
  exact h.2

theorem ttFiber4ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 9) (ttFiber4StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 9) (ttFiber4StateAt 25)
      (ttFiber4RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 25) (by decide) ttFiber4ReverseRow_25_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_26_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk13] at h
  exact h.1

theorem ttFiber4ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 10) (ttFiber4StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 10) (ttFiber4StateAt 26)
      (ttFiber4RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 26) (by decide) ttFiber4ReverseRow_26_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_27_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk13] at h
  exact h.2

theorem ttFiber4ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 11) (ttFiber4StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 11) (ttFiber4StateAt 27)
      (ttFiber4RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 27) (by decide) ttFiber4ReverseRow_27_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_28_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk14] at h
  exact h.1

theorem ttFiber4ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 24) (ttFiber4StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 24) (ttFiber4StateAt 28)
      (ttFiber4RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 28) (by decide) ttFiber4ReverseRow_28_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_29_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk14] at h
  exact h.2

theorem ttFiber4ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 25) (ttFiber4StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 25) (ttFiber4StateAt 29)
      (ttFiber4RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 29) (by decide) ttFiber4ReverseRow_29_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_30_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk15] at h
  exact h.1

theorem ttFiber4ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 14) (ttFiber4StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 14) (ttFiber4StateAt 30)
      (ttFiber4RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 30) (by decide) ttFiber4ReverseRow_30_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_31_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk15] at h
  exact h.2

theorem ttFiber4ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 15) (ttFiber4StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 15) (ttFiber4StateAt 31)
      (ttFiber4RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 31) (by decide) ttFiber4ReverseRow_31_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_32_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk16] at h
  exact h.1

theorem ttFiber4ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 48) (ttFiber4StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 48) (ttFiber4StateAt 32)
      (ttFiber4RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 32) (by decide) ttFiber4ReverseRow_32_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_33_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk16] at h
  exact h.2

theorem ttFiber4ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 49) (ttFiber4StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 49) (ttFiber4StateAt 33)
      (ttFiber4RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 33) (by decide) ttFiber4ReverseRow_33_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_34_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk17] at h
  exact h.1

theorem ttFiber4ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 22) (ttFiber4StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 22) (ttFiber4StateAt 34)
      (ttFiber4RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 34) (by decide) ttFiber4ReverseRow_34_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_35_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk17] at h
  exact h.2

theorem ttFiber4ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 23) (ttFiber4StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 23) (ttFiber4StateAt 35)
      (ttFiber4RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 35) (by decide) ttFiber4ReverseRow_35_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_36_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk18] at h
  exact h.1

theorem ttFiber4ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 18) (ttFiber4StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 18) (ttFiber4StateAt 36)
      (ttFiber4RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 36) (by decide) ttFiber4ReverseRow_36_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_37_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk18] at h
  exact h.2

theorem ttFiber4ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 39) (ttFiber4StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 39) (ttFiber4StateAt 37)
      (ttFiber4RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 37) (by decide) ttFiber4ReverseRow_37_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_38_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk19] at h
  exact h.1

theorem ttFiber4ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 17) (ttFiber4StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 17) (ttFiber4StateAt 38)
      (ttFiber4RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 38) (by decide) ttFiber4ReverseRow_38_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_39_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk19] at h
  exact h.2

theorem ttFiber4ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 16) (ttFiber4StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 16) (ttFiber4StateAt 39)
      (ttFiber4RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 39) (by decide) ttFiber4ReverseRow_39_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_40_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk20] at h
  exact h.1

theorem ttFiber4ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 56) (ttFiber4StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 56) (ttFiber4StateAt 40)
      (ttFiber4RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 40) (by decide) ttFiber4ReverseRow_40_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_41_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk20] at h
  exact h.2

theorem ttFiber4ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 57) (ttFiber4StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 57) (ttFiber4StateAt 41)
      (ttFiber4RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 41) (by decide) ttFiber4ReverseRow_41_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_42_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk21] at h
  exact h.1

theorem ttFiber4ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 58) (ttFiber4StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 58) (ttFiber4StateAt 42)
      (ttFiber4RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 42) (by decide) ttFiber4ReverseRow_42_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_43_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk21] at h
  exact h.2

theorem ttFiber4ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 40) (ttFiber4StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 40) (ttFiber4StateAt 43)
      (ttFiber4RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 43) (by decide) ttFiber4ReverseRow_43_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_44_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk22] at h
  exact h.1

theorem ttFiber4ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 40) (ttFiber4StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 40) (ttFiber4StateAt 44)
      (ttFiber4RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 44) (by decide) ttFiber4ReverseRow_44_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_45_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk22] at h
  exact h.2

theorem ttFiber4ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 41) (ttFiber4StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 41) (ttFiber4StateAt 45)
      (ttFiber4RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 45) (by decide) ttFiber4ReverseRow_45_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_46_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk23] at h
  exact h.1

theorem ttFiber4ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 62) (ttFiber4StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 62) (ttFiber4StateAt 46)
      (ttFiber4RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 46) (by decide) ttFiber4ReverseRow_46_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_47_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk23] at h
  exact h.2

theorem ttFiber4ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 63) (ttFiber4StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 63) (ttFiber4StateAt 47)
      (ttFiber4RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 47) (by decide) ttFiber4ReverseRow_47_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_48_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk24] at h
  exact h.1

theorem ttFiber4ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 8) (ttFiber4StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 8) (ttFiber4StateAt 48)
      (ttFiber4RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 48) (by decide) ttFiber4ReverseRow_48_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_49_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk24] at h
  exact h.2

theorem ttFiber4ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 9) (ttFiber4StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 9) (ttFiber4StateAt 49)
      (ttFiber4RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 49) (by decide) ttFiber4ReverseRow_49_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_50_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk25] at h
  exact h.1

theorem ttFiber4ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 10) (ttFiber4StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 10) (ttFiber4StateAt 50)
      (ttFiber4RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 50) (by decide) ttFiber4ReverseRow_50_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_51_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk25] at h
  exact h.2

theorem ttFiber4ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 11) (ttFiber4StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 11) (ttFiber4StateAt 51)
      (ttFiber4RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 51) (by decide) ttFiber4ReverseRow_51_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_52_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk26] at h
  exact h.1

theorem ttFiber4ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 12) (ttFiber4StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 12) (ttFiber4StateAt 52)
      (ttFiber4RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 52) (by decide) ttFiber4ReverseRow_52_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_53_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk26] at h
  exact h.2

theorem ttFiber4ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 13) (ttFiber4StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 13) (ttFiber4StateAt 53)
      (ttFiber4RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 53) (by decide) ttFiber4ReverseRow_53_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_54_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk27] at h
  exact h.1

theorem ttFiber4ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 14) (ttFiber4StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 14) (ttFiber4StateAt 54)
      (ttFiber4RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 54) (by decide) ttFiber4ReverseRow_54_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_55_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk27] at h
  exact h.2

theorem ttFiber4ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 15) (ttFiber4StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 15) (ttFiber4StateAt 55)
      (ttFiber4RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 55) (by decide) ttFiber4ReverseRow_55_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_56_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk28] at h
  exact h.1

theorem ttFiber4ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 0) (ttFiber4StateAt 56)
      (ttFiber4RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 56) (by decide) ttFiber4ReverseRow_56_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_57_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk28] at h
  exact h.2

theorem ttFiber4ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 1) (ttFiber4StateAt 57)
      (ttFiber4RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 57) (by decide) ttFiber4ReverseRow_57_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_58_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk29] at h
  exact h.1

theorem ttFiber4ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 2) (ttFiber4StateAt 58)
      (ttFiber4RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 58) (by decide) ttFiber4ReverseRow_58_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_59_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk29] at h
  exact h.2

theorem ttFiber4ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 3) (ttFiber4StateAt 59)
      (ttFiber4RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 59) (by decide) ttFiber4ReverseRow_59_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_60_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk30] at h
  exact h.1

theorem ttFiber4ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 4) (ttFiber4StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 4) (ttFiber4StateAt 60)
      (ttFiber4RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 60) (by decide) ttFiber4ReverseRow_60_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_61_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk30] at h
  exact h.2

theorem ttFiber4ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 5) (ttFiber4StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 5) (ttFiber4StateAt 61)
      (ttFiber4RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 61) (by decide) ttFiber4ReverseRow_61_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_62_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk31] at h
  exact h.1

theorem ttFiber4ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 6) (ttFiber4StateAt 62)
      (ttFiber4RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 62) (by decide) ttFiber4ReverseRow_62_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4ReverseRow_63_ok' :
    directRowReverseValid ttFiber4Key ttFiber4Expected (ttFiber4RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber4Chunk31] at h
  exact h.2

theorem ttFiber4ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber4StateAt 7) (ttFiber4StateAt 63)
      (ttFiber4RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber4Key ttFiber4Expected
      (ttFiber4RowAt 63) (by decide) ttFiber4ReverseRow_63_ok'
    simpa [ttFiber4StateAt, ttFiber4RowAt, ttFiber4Rows, listGetD, directRow] using h

theorem ttFiber4FirstPassGrows :
    ((chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]).length ==
      [ttFiber4StateAt 0].length) = false := by
  have hroot : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber4DirectStates [ttFiber4StateAt 0]
      (ttFiber4StateAt 0) (by simp)
  have hnew : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber4DirectStates [ttFiber4StateAt 0]
      (ttFiber4StateAt 0) (ttFiber4StateAt 1) (by decide) (by simp)
      ttFiber4ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0])
    (ttFiber4StateAt 0) (ttFiber4StateAt 1) hroot hnew (by decide)

theorem ttFiber4State0_in_pass0_full :
    ttFiber4StateAt 0 ∈ [ttFiber4StateAt 0] := by
  simp

theorem ttFiber4State1_in_pass1_prefix1 :
    ttFiber4StateAt 1 ∈ chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix0 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix0
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix1 = ttFiber4Prefix0 ++ [ttFiber4StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 1) []
    (chainClosureStep ttWord ttFiber4Prefix0 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep1

theorem ttFiber4State1_in_pass1_full :
    ttFiber4StateAt 1 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix1 ++ [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1

theorem ttFiber4State2_in_pass1_prefix2 :
    ttFiber4StateAt 2 ∈ chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix1
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix2 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 2) []
    (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep2

theorem ttFiber4State2_in_pass1_full :
    ttFiber4StateAt 2 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix2 ++ [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 2) ttFiber4State2_in_pass1_prefix2

theorem ttFiber4State3_in_pass1_prefix3 :
    ttFiber4StateAt 3 ∈ chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix2 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2]
      (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1
  rw [show ttFiber4Prefix3 = ttFiber4Prefix2 ++ [ttFiber4StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 3) []
    (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) hparentBefore ttFiber4ReverseSingleStep3

theorem ttFiber4State3_in_pass1_full :
    ttFiber4StateAt 3 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix3 ++ [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 3) ttFiber4State3_in_pass1_prefix3

theorem ttFiber4State4_in_pass1_prefix4 :
    ttFiber4StateAt 4 ∈ chainClosureStep ttWord ttFiber4Prefix4 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 2 ∈
      chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix3 = ttFiber4Prefix2 ++ [ttFiber4StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 3]
      (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 2) ttFiber4State2_in_pass1_prefix2
  rw [show ttFiber4Prefix4 = ttFiber4Prefix3 ++ [ttFiber4StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 4) []
    (chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 2) hparentBefore ttFiber4ReverseSingleStep4

theorem ttFiber4State4_in_pass1_full :
    ttFiber4StateAt 4 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix4 ++ [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix4 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 4) ttFiber4State4_in_pass1_prefix4

theorem ttFiber4State6_in_pass1_prefix6 :
    ttFiber4StateAt 6 ∈ chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4Prefix5 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix5 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5]
      (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1
  rw [show ttFiber4Prefix6 = ttFiber4Prefix5 ++ [ttFiber4StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 6) []
    (chainClosureStep ttWord ttFiber4Prefix5 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) hparentBefore ttFiber4ReverseSingleStep6

theorem ttFiber4State6_in_pass1_full :
    ttFiber4StateAt 6 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix6 ++ [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 6) ttFiber4State6_in_pass1_prefix6

theorem ttFiber4State7_in_pass1_prefix7 :
    ttFiber4StateAt 7 ∈ chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix6
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix7 = ttFiber4Prefix6 ++ [ttFiber4StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 7) []
    (chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep7

theorem ttFiber4State7_in_pass1_full :
    ttFiber4StateAt 7 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix7 ++ [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 7) ttFiber4State7_in_pass1_prefix7

theorem ttFiber4State8_in_pass1_prefix8 :
    ttFiber4StateAt 8 ∈ chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix7
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix8 = ttFiber4Prefix7 ++ [ttFiber4StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 8) []
    (chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep8

theorem ttFiber4State8_in_pass1_full :
    ttFiber4StateAt 8 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix8 ++ [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 8) ttFiber4State8_in_pass1_prefix8

theorem ttFiber4State9_in_pass1_prefix9 :
    ttFiber4StateAt 9 ∈ chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix8 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8]
      (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1
  rw [show ttFiber4Prefix9 = ttFiber4Prefix8 ++ [ttFiber4StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 9) []
    (chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) hparentBefore ttFiber4ReverseSingleStep9

theorem ttFiber4State9_in_pass1_full :
    ttFiber4StateAt 9 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix9 ++ [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 9) ttFiber4State9_in_pass1_prefix9

theorem ttFiber4State10_in_pass1_prefix10 :
    ttFiber4StateAt 10 ∈ chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 2 ∈
      chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix9 = ttFiber4Prefix2 ++ [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9]
      (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 2) ttFiber4State2_in_pass1_prefix2
  rw [show ttFiber4Prefix10 = ttFiber4Prefix9 ++ [ttFiber4StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 10) []
    (chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 2) hparentBefore ttFiber4ReverseSingleStep10

theorem ttFiber4State10_in_pass1_full :
    ttFiber4StateAt 10 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix10 ++ [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 10) ttFiber4State10_in_pass1_prefix10

theorem ttFiber4State11_in_pass1_prefix11 :
    ttFiber4StateAt 11 ∈ chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 3 ∈
      chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix10 = ttFiber4Prefix3 ++ [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10]
      (chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 3) ttFiber4State3_in_pass1_prefix3
  rw [show ttFiber4Prefix11 = ttFiber4Prefix10 ++ [ttFiber4StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 11) []
    (chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 3) hparentBefore ttFiber4ReverseSingleStep11

theorem ttFiber4State11_in_pass1_full :
    ttFiber4StateAt 11 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix11 ++ [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 11) ttFiber4State11_in_pass1_prefix11

theorem ttFiber4State12_in_pass1_prefix12 :
    ttFiber4StateAt 12 ∈ chainClosureStep ttWord ttFiber4Prefix12 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 4 ∈
      chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix11 = ttFiber4Prefix4 ++ [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11]
      (chainClosureStep ttWord ttFiber4Prefix4 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 4) ttFiber4State4_in_pass1_prefix4
  rw [show ttFiber4Prefix12 = ttFiber4Prefix11 ++ [ttFiber4StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 12) []
    (chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 4) hparentBefore ttFiber4ReverseSingleStep12

theorem ttFiber4State12_in_pass1_full :
    ttFiber4StateAt 12 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix12 ++ [ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix12 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 12) ttFiber4State12_in_pass1_prefix12

theorem ttFiber4State14_in_pass1_prefix14 :
    ttFiber4StateAt 14 ∈ chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 6 ∈
      chainClosureStep ttWord ttFiber4Prefix13 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix13 = ttFiber4Prefix6 ++ [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13]
      (chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 6) ttFiber4State6_in_pass1_prefix6
  rw [show ttFiber4Prefix14 = ttFiber4Prefix13 ++ [ttFiber4StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 14) []
    (chainClosureStep ttWord ttFiber4Prefix13 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 6) hparentBefore ttFiber4ReverseSingleStep14

theorem ttFiber4State14_in_pass1_full :
    ttFiber4StateAt 14 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix14 ++ [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 14) ttFiber4State14_in_pass1_prefix14

theorem ttFiber4State15_in_pass1_prefix15 :
    ttFiber4StateAt 15 ∈ chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 7 ∈
      chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix14 = ttFiber4Prefix7 ++ [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14]
      (chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 7) ttFiber4State7_in_pass1_prefix7
  rw [show ttFiber4Prefix15 = ttFiber4Prefix14 ++ [ttFiber4StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 15) []
    (chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 7) hparentBefore ttFiber4ReverseSingleStep15

theorem ttFiber4State15_in_pass1_full :
    ttFiber4StateAt 15 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix15 ++ [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 15) ttFiber4State15_in_pass1_prefix15

theorem ttFiber4State16_in_pass1_prefix16 :
    ttFiber4StateAt 16 ∈ chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix15
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix16 = ttFiber4Prefix15 ++ [ttFiber4StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 16) []
    (chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep16

theorem ttFiber4State16_in_pass1_full :
    ttFiber4StateAt 16 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix16 ++ [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 16) ttFiber4State16_in_pass1_prefix16

theorem ttFiber4State17_in_pass1_prefix17 :
    ttFiber4StateAt 17 ∈ chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix16 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16]
      (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1
  rw [show ttFiber4Prefix17 = ttFiber4Prefix16 ++ [ttFiber4StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 17) []
    (chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) hparentBefore ttFiber4ReverseSingleStep17

theorem ttFiber4State17_in_pass1_full :
    ttFiber4StateAt 17 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix17 ++ [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 17) ttFiber4State17_in_pass1_prefix17

theorem ttFiber4State18_in_pass1_prefix18 :
    ttFiber4StateAt 18 ∈ chainClosureStep ttWord ttFiber4Prefix18 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 2 ∈
      chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix17 = ttFiber4Prefix2 ++ [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17]
      (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 2) ttFiber4State2_in_pass1_prefix2
  rw [show ttFiber4Prefix18 = ttFiber4Prefix17 ++ [ttFiber4StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 18) []
    (chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 2) hparentBefore ttFiber4ReverseSingleStep18

theorem ttFiber4State18_in_pass1_full :
    ttFiber4StateAt 18 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix18 ++ [ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix18 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 18) ttFiber4State18_in_pass1_prefix18

theorem ttFiber4State19_in_pass1_prefix19 :
    ttFiber4StateAt 19 ∈ chainClosureStep ttWord ttFiber4Prefix19 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 3 ∈
      chainClosureStep ttWord ttFiber4Prefix18 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix18 = ttFiber4Prefix3 ++ [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18]
      (chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 3) ttFiber4State3_in_pass1_prefix3
  rw [show ttFiber4Prefix19 = ttFiber4Prefix18 ++ [ttFiber4StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 19) []
    (chainClosureStep ttWord ttFiber4Prefix18 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 3) hparentBefore ttFiber4ReverseSingleStep19

theorem ttFiber4State19_in_pass1_full :
    ttFiber4StateAt 19 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix19 ++ [ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix19 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 19) ttFiber4State19_in_pass1_prefix19

theorem ttFiber4State20_in_pass1_prefix20 :
    ttFiber4StateAt 20 ∈ chainClosureStep ttWord ttFiber4Prefix20 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 16 ∈
      chainClosureStep ttWord ttFiber4Prefix19 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix19 = ttFiber4Prefix16 ++ [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19]
      (chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 16) ttFiber4State16_in_pass1_prefix16
  rw [show ttFiber4Prefix20 = ttFiber4Prefix19 ++ [ttFiber4StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 20) []
    (chainClosureStep ttWord ttFiber4Prefix19 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 16) hparentBefore ttFiber4ReverseSingleStep20

theorem ttFiber4State20_in_pass1_full :
    ttFiber4StateAt 20 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix20 ++ [ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix20 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 20) ttFiber4State20_in_pass1_prefix20

theorem ttFiber4State21_in_pass1_prefix21 :
    ttFiber4StateAt 21 ∈ chainClosureStep ttWord ttFiber4Prefix21 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 17 ∈
      chainClosureStep ttWord ttFiber4Prefix20 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix20 = ttFiber4Prefix17 ++ [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20]
      (chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 17) ttFiber4State17_in_pass1_prefix17
  rw [show ttFiber4Prefix21 = ttFiber4Prefix20 ++ [ttFiber4StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 21) []
    (chainClosureStep ttWord ttFiber4Prefix20 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 17) hparentBefore ttFiber4ReverseSingleStep21

theorem ttFiber4State21_in_pass1_full :
    ttFiber4StateAt 21 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix21 ++ [ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix21 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 21) ttFiber4State21_in_pass1_prefix21

theorem ttFiber4State22_in_pass1_prefix22 :
    ttFiber4StateAt 22 ∈ chainClosureStep ttWord ttFiber4Prefix22 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 6 ∈
      chainClosureStep ttWord ttFiber4Prefix21 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix21 = ttFiber4Prefix6 ++ [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21]
      (chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 6) ttFiber4State6_in_pass1_prefix6
  rw [show ttFiber4Prefix22 = ttFiber4Prefix21 ++ [ttFiber4StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 22) []
    (chainClosureStep ttWord ttFiber4Prefix21 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 6) hparentBefore ttFiber4ReverseSingleStep22

theorem ttFiber4State22_in_pass1_full :
    ttFiber4StateAt 22 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix22 ++ [ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix22 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 22) ttFiber4State22_in_pass1_prefix22

theorem ttFiber4State23_in_pass1_prefix23 :
    ttFiber4StateAt 23 ∈ chainClosureStep ttWord ttFiber4Prefix23 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 7 ∈
      chainClosureStep ttWord ttFiber4Prefix22 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix22 = ttFiber4Prefix7 ++ [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22]
      (chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 7) ttFiber4State7_in_pass1_prefix7
  rw [show ttFiber4Prefix23 = ttFiber4Prefix22 ++ [ttFiber4StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 23) []
    (chainClosureStep ttWord ttFiber4Prefix22 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 7) hparentBefore ttFiber4ReverseSingleStep23

theorem ttFiber4State23_in_pass1_full :
    ttFiber4StateAt 23 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix23 ++ [ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix23 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 23) ttFiber4State23_in_pass1_prefix23

theorem ttFiber4State24_in_pass1_prefix24 :
    ttFiber4StateAt 24 ∈ chainClosureStep ttWord ttFiber4Prefix24 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 8 ∈
      chainClosureStep ttWord ttFiber4Prefix23 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix23 = ttFiber4Prefix8 ++ [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23]
      (chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 8) ttFiber4State8_in_pass1_prefix8
  rw [show ttFiber4Prefix24 = ttFiber4Prefix23 ++ [ttFiber4StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 24) []
    (chainClosureStep ttWord ttFiber4Prefix23 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 8) hparentBefore ttFiber4ReverseSingleStep24

theorem ttFiber4State24_in_pass1_full :
    ttFiber4StateAt 24 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix24 ++ [ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix24 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 24) ttFiber4State24_in_pass1_prefix24

theorem ttFiber4State25_in_pass1_prefix25 :
    ttFiber4StateAt 25 ∈ chainClosureStep ttWord ttFiber4Prefix25 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 9 ∈
      chainClosureStep ttWord ttFiber4Prefix24 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix24 = ttFiber4Prefix9 ++ [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24]
      (chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 9) ttFiber4State9_in_pass1_prefix9
  rw [show ttFiber4Prefix25 = ttFiber4Prefix24 ++ [ttFiber4StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 25) []
    (chainClosureStep ttWord ttFiber4Prefix24 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 9) hparentBefore ttFiber4ReverseSingleStep25

theorem ttFiber4State25_in_pass1_full :
    ttFiber4StateAt 25 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix25 ++ [ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix25 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 25) ttFiber4State25_in_pass1_prefix25

theorem ttFiber4State26_in_pass1_prefix26 :
    ttFiber4StateAt 26 ∈ chainClosureStep ttWord ttFiber4Prefix26 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 10 ∈
      chainClosureStep ttWord ttFiber4Prefix25 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix25 = ttFiber4Prefix10 ++ [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25]
      (chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 10) ttFiber4State10_in_pass1_prefix10
  rw [show ttFiber4Prefix26 = ttFiber4Prefix25 ++ [ttFiber4StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 26) []
    (chainClosureStep ttWord ttFiber4Prefix25 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 10) hparentBefore ttFiber4ReverseSingleStep26

theorem ttFiber4State26_in_pass1_full :
    ttFiber4StateAt 26 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix26 ++ [ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix26 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 26) ttFiber4State26_in_pass1_prefix26

theorem ttFiber4State27_in_pass1_prefix27 :
    ttFiber4StateAt 27 ∈ chainClosureStep ttWord ttFiber4Prefix27 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 11 ∈
      chainClosureStep ttWord ttFiber4Prefix26 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix26 = ttFiber4Prefix11 ++ [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26]
      (chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 11) ttFiber4State11_in_pass1_prefix11
  rw [show ttFiber4Prefix27 = ttFiber4Prefix26 ++ [ttFiber4StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 27) []
    (chainClosureStep ttWord ttFiber4Prefix26 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 11) hparentBefore ttFiber4ReverseSingleStep27

theorem ttFiber4State27_in_pass1_full :
    ttFiber4StateAt 27 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix27 ++ [ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix27 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 27) ttFiber4State27_in_pass1_prefix27

theorem ttFiber4State28_in_pass1_prefix28 :
    ttFiber4StateAt 28 ∈ chainClosureStep ttWord ttFiber4Prefix28 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 24 ∈
      chainClosureStep ttWord ttFiber4Prefix27 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix27 = ttFiber4Prefix24 ++ [ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27]
      (chainClosureStep ttWord ttFiber4Prefix24 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 24) ttFiber4State24_in_pass1_prefix24
  rw [show ttFiber4Prefix28 = ttFiber4Prefix27 ++ [ttFiber4StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 28) []
    (chainClosureStep ttWord ttFiber4Prefix27 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 24) hparentBefore ttFiber4ReverseSingleStep28

theorem ttFiber4State28_in_pass1_full :
    ttFiber4StateAt 28 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix28 ++ [ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix28 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 28) ttFiber4State28_in_pass1_prefix28

theorem ttFiber4State29_in_pass1_prefix29 :
    ttFiber4StateAt 29 ∈ chainClosureStep ttWord ttFiber4Prefix29 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 25 ∈
      chainClosureStep ttWord ttFiber4Prefix28 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix28 = ttFiber4Prefix25 ++ [ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28]
      (chainClosureStep ttWord ttFiber4Prefix25 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 25) ttFiber4State25_in_pass1_prefix25
  rw [show ttFiber4Prefix29 = ttFiber4Prefix28 ++ [ttFiber4StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 29) []
    (chainClosureStep ttWord ttFiber4Prefix28 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 25) hparentBefore ttFiber4ReverseSingleStep29

theorem ttFiber4State29_in_pass1_full :
    ttFiber4StateAt 29 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix29 ++ [ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix29 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 29) ttFiber4State29_in_pass1_prefix29

theorem ttFiber4State30_in_pass1_prefix30 :
    ttFiber4StateAt 30 ∈ chainClosureStep ttWord ttFiber4Prefix30 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 14 ∈
      chainClosureStep ttWord ttFiber4Prefix29 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix29 = ttFiber4Prefix14 ++ [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29]
      (chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 14) ttFiber4State14_in_pass1_prefix14
  rw [show ttFiber4Prefix30 = ttFiber4Prefix29 ++ [ttFiber4StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 30) []
    (chainClosureStep ttWord ttFiber4Prefix29 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 14) hparentBefore ttFiber4ReverseSingleStep30

theorem ttFiber4State30_in_pass1_full :
    ttFiber4StateAt 30 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix30 ++ [ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix30 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 30) ttFiber4State30_in_pass1_prefix30

theorem ttFiber4State31_in_pass1_prefix31 :
    ttFiber4StateAt 31 ∈ chainClosureStep ttWord ttFiber4Prefix31 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 15 ∈
      chainClosureStep ttWord ttFiber4Prefix30 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix30 = ttFiber4Prefix15 ++ [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30]
      (chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 15) ttFiber4State15_in_pass1_prefix15
  rw [show ttFiber4Prefix31 = ttFiber4Prefix30 ++ [ttFiber4StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 31) []
    (chainClosureStep ttWord ttFiber4Prefix30 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 15) hparentBefore ttFiber4ReverseSingleStep31

theorem ttFiber4State31_in_pass1_full :
    ttFiber4StateAt 31 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix31 ++ [ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix31 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 31) ttFiber4State31_in_pass1_prefix31

theorem ttFiber4State34_in_pass1_prefix34 :
    ttFiber4StateAt 34 ∈ chainClosureStep ttWord ttFiber4Prefix34 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 22 ∈
      chainClosureStep ttWord ttFiber4Prefix33 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix33 = ttFiber4Prefix22 ++ [ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33]
      (chainClosureStep ttWord ttFiber4Prefix22 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 22) ttFiber4State22_in_pass1_prefix22
  rw [show ttFiber4Prefix34 = ttFiber4Prefix33 ++ [ttFiber4StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 34) []
    (chainClosureStep ttWord ttFiber4Prefix33 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 22) hparentBefore ttFiber4ReverseSingleStep34

theorem ttFiber4State34_in_pass1_full :
    ttFiber4StateAt 34 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix34 ++ [ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix34 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 34) ttFiber4State34_in_pass1_prefix34

theorem ttFiber4State35_in_pass1_prefix35 :
    ttFiber4StateAt 35 ∈ chainClosureStep ttWord ttFiber4Prefix35 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 23 ∈
      chainClosureStep ttWord ttFiber4Prefix34 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix34 = ttFiber4Prefix23 ++ [ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34]
      (chainClosureStep ttWord ttFiber4Prefix23 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 23) ttFiber4State23_in_pass1_prefix23
  rw [show ttFiber4Prefix35 = ttFiber4Prefix34 ++ [ttFiber4StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 35) []
    (chainClosureStep ttWord ttFiber4Prefix34 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 23) hparentBefore ttFiber4ReverseSingleStep35

theorem ttFiber4State35_in_pass1_full :
    ttFiber4StateAt 35 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix35 ++ [ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix35 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 35) ttFiber4State35_in_pass1_prefix35

theorem ttFiber4State36_in_pass1_prefix36 :
    ttFiber4StateAt 36 ∈ chainClosureStep ttWord ttFiber4Prefix36 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 18 ∈
      chainClosureStep ttWord ttFiber4Prefix35 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix35 = ttFiber4Prefix18 ++ [ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35]
      (chainClosureStep ttWord ttFiber4Prefix18 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 18) ttFiber4State18_in_pass1_prefix18
  rw [show ttFiber4Prefix36 = ttFiber4Prefix35 ++ [ttFiber4StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 36) []
    (chainClosureStep ttWord ttFiber4Prefix35 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 18) hparentBefore ttFiber4ReverseSingleStep36

theorem ttFiber4State36_in_pass1_full :
    ttFiber4StateAt 36 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix36 ++ [ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix36 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 36) ttFiber4State36_in_pass1_prefix36

theorem ttFiber4State38_in_pass1_prefix38 :
    ttFiber4StateAt 38 ∈ chainClosureStep ttWord ttFiber4Prefix38 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 17 ∈
      chainClosureStep ttWord ttFiber4Prefix37 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix37 = ttFiber4Prefix17 ++ [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37]
      (chainClosureStep ttWord ttFiber4Prefix17 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 17) ttFiber4State17_in_pass1_prefix17
  rw [show ttFiber4Prefix38 = ttFiber4Prefix37 ++ [ttFiber4StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 38) []
    (chainClosureStep ttWord ttFiber4Prefix37 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 17) hparentBefore ttFiber4ReverseSingleStep38

theorem ttFiber4State38_in_pass1_full :
    ttFiber4StateAt 38 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix38 ++ [ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix38 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 38) ttFiber4State38_in_pass1_prefix38

theorem ttFiber4State39_in_pass1_prefix39 :
    ttFiber4StateAt 39 ∈ chainClosureStep ttWord ttFiber4Prefix39 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 16 ∈
      chainClosureStep ttWord ttFiber4Prefix38 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix38 = ttFiber4Prefix16 ++ [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38]
      (chainClosureStep ttWord ttFiber4Prefix16 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 16) ttFiber4State16_in_pass1_prefix16
  rw [show ttFiber4Prefix39 = ttFiber4Prefix38 ++ [ttFiber4StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 39) []
    (chainClosureStep ttWord ttFiber4Prefix38 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 16) hparentBefore ttFiber4ReverseSingleStep39

theorem ttFiber4State39_in_pass1_full :
    ttFiber4StateAt 39 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix39 ++ [ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix39 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 39) ttFiber4State39_in_pass1_prefix39

theorem ttFiber4State48_in_pass1_prefix48 :
    ttFiber4StateAt 48 ∈ chainClosureStep ttWord ttFiber4Prefix48 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 8 ∈
      chainClosureStep ttWord ttFiber4Prefix47 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix47 = ttFiber4Prefix8 ++ [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47]
      (chainClosureStep ttWord ttFiber4Prefix8 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 8) ttFiber4State8_in_pass1_prefix8
  rw [show ttFiber4Prefix48 = ttFiber4Prefix47 ++ [ttFiber4StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 48) []
    (chainClosureStep ttWord ttFiber4Prefix47 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 8) hparentBefore ttFiber4ReverseSingleStep48

theorem ttFiber4State48_in_pass1_full :
    ttFiber4StateAt 48 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix48 ++ [ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix48 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 48) ttFiber4State48_in_pass1_prefix48

theorem ttFiber4State49_in_pass1_prefix49 :
    ttFiber4StateAt 49 ∈ chainClosureStep ttWord ttFiber4Prefix49 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 9 ∈
      chainClosureStep ttWord ttFiber4Prefix48 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix48 = ttFiber4Prefix9 ++ [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48]
      (chainClosureStep ttWord ttFiber4Prefix9 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 9) ttFiber4State9_in_pass1_prefix9
  rw [show ttFiber4Prefix49 = ttFiber4Prefix48 ++ [ttFiber4StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 49) []
    (chainClosureStep ttWord ttFiber4Prefix48 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 9) hparentBefore ttFiber4ReverseSingleStep49

theorem ttFiber4State49_in_pass1_full :
    ttFiber4StateAt 49 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix49 ++ [ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix49 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 49) ttFiber4State49_in_pass1_prefix49

theorem ttFiber4State50_in_pass1_prefix50 :
    ttFiber4StateAt 50 ∈ chainClosureStep ttWord ttFiber4Prefix50 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 10 ∈
      chainClosureStep ttWord ttFiber4Prefix49 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix49 = ttFiber4Prefix10 ++ [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49]
      (chainClosureStep ttWord ttFiber4Prefix10 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 10) ttFiber4State10_in_pass1_prefix10
  rw [show ttFiber4Prefix50 = ttFiber4Prefix49 ++ [ttFiber4StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 50) []
    (chainClosureStep ttWord ttFiber4Prefix49 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 10) hparentBefore ttFiber4ReverseSingleStep50

theorem ttFiber4State50_in_pass1_full :
    ttFiber4StateAt 50 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix50 ++ [ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix50 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 50) ttFiber4State50_in_pass1_prefix50

theorem ttFiber4State51_in_pass1_prefix51 :
    ttFiber4StateAt 51 ∈ chainClosureStep ttWord ttFiber4Prefix51 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 11 ∈
      chainClosureStep ttWord ttFiber4Prefix50 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix50 = ttFiber4Prefix11 ++ [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50]
      (chainClosureStep ttWord ttFiber4Prefix11 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 11) ttFiber4State11_in_pass1_prefix11
  rw [show ttFiber4Prefix51 = ttFiber4Prefix50 ++ [ttFiber4StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 51) []
    (chainClosureStep ttWord ttFiber4Prefix50 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 11) hparentBefore ttFiber4ReverseSingleStep51

theorem ttFiber4State51_in_pass1_full :
    ttFiber4StateAt 51 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix51 ++ [ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix51 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 51) ttFiber4State51_in_pass1_prefix51

theorem ttFiber4State52_in_pass1_prefix52 :
    ttFiber4StateAt 52 ∈ chainClosureStep ttWord ttFiber4Prefix52 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 12 ∈
      chainClosureStep ttWord ttFiber4Prefix51 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix51 = ttFiber4Prefix12 ++ [ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51]
      (chainClosureStep ttWord ttFiber4Prefix12 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 12) ttFiber4State12_in_pass1_prefix12
  rw [show ttFiber4Prefix52 = ttFiber4Prefix51 ++ [ttFiber4StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 52) []
    (chainClosureStep ttWord ttFiber4Prefix51 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 12) hparentBefore ttFiber4ReverseSingleStep52

theorem ttFiber4State52_in_pass1_full :
    ttFiber4StateAt 52 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix52 ++ [ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix52 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 52) ttFiber4State52_in_pass1_prefix52

theorem ttFiber4State54_in_pass1_prefix54 :
    ttFiber4StateAt 54 ∈ chainClosureStep ttWord ttFiber4Prefix54 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 14 ∈
      chainClosureStep ttWord ttFiber4Prefix53 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix53 = ttFiber4Prefix14 ++ [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53]
      (chainClosureStep ttWord ttFiber4Prefix14 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 14) ttFiber4State14_in_pass1_prefix14
  rw [show ttFiber4Prefix54 = ttFiber4Prefix53 ++ [ttFiber4StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 54) []
    (chainClosureStep ttWord ttFiber4Prefix53 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 14) hparentBefore ttFiber4ReverseSingleStep54

theorem ttFiber4State54_in_pass1_full :
    ttFiber4StateAt 54 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix54 ++ [ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix54 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 54) ttFiber4State54_in_pass1_prefix54

theorem ttFiber4State55_in_pass1_prefix55 :
    ttFiber4StateAt 55 ∈ chainClosureStep ttWord ttFiber4Prefix55 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 15 ∈
      chainClosureStep ttWord ttFiber4Prefix54 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix54 = ttFiber4Prefix15 ++ [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54]
      (chainClosureStep ttWord ttFiber4Prefix15 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 15) ttFiber4State15_in_pass1_prefix15
  rw [show ttFiber4Prefix55 = ttFiber4Prefix54 ++ [ttFiber4StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 55) []
    (chainClosureStep ttWord ttFiber4Prefix54 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 15) hparentBefore ttFiber4ReverseSingleStep55

theorem ttFiber4State55_in_pass1_full :
    ttFiber4StateAt 55 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix55 ++ [ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix55 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 55) ttFiber4State55_in_pass1_prefix55

theorem ttFiber4State56_in_pass1_prefix56 :
    ttFiber4StateAt 56 ∈ chainClosureStep ttWord ttFiber4Prefix56 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 0 ∈
      chainClosureStep ttWord ttFiber4Prefix55 ([ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix55
      ([ttFiber4StateAt 0]) (ttFiber4StateAt 0) ttFiber4State0_in_pass0_full
  rw [show ttFiber4Prefix56 = ttFiber4Prefix55 ++ [ttFiber4StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 56) []
    (chainClosureStep ttWord ttFiber4Prefix55 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 0) hparentBefore ttFiber4ReverseSingleStep56

theorem ttFiber4State56_in_pass1_full :
    ttFiber4StateAt 56 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix56 ++ [ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix56 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 56) ttFiber4State56_in_pass1_prefix56

theorem ttFiber4State57_in_pass1_prefix57 :
    ttFiber4StateAt 57 ∈ chainClosureStep ttWord ttFiber4Prefix57 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 1 ∈
      chainClosureStep ttWord ttFiber4Prefix56 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix56 = ttFiber4Prefix1 ++ [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 2, ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56]
      (chainClosureStep ttWord ttFiber4Prefix1 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 1) ttFiber4State1_in_pass1_prefix1
  rw [show ttFiber4Prefix57 = ttFiber4Prefix56 ++ [ttFiber4StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 57) []
    (chainClosureStep ttWord ttFiber4Prefix56 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 1) hparentBefore ttFiber4ReverseSingleStep57

theorem ttFiber4State57_in_pass1_full :
    ttFiber4StateAt 57 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix57 ++ [ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix57 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 57) ttFiber4State57_in_pass1_prefix57

theorem ttFiber4State58_in_pass1_prefix58 :
    ttFiber4StateAt 58 ∈ chainClosureStep ttWord ttFiber4Prefix58 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 2 ∈
      chainClosureStep ttWord ttFiber4Prefix57 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix57 = ttFiber4Prefix2 ++ [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 3, ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57]
      (chainClosureStep ttWord ttFiber4Prefix2 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 2) ttFiber4State2_in_pass1_prefix2
  rw [show ttFiber4Prefix58 = ttFiber4Prefix57 ++ [ttFiber4StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 58) []
    (chainClosureStep ttWord ttFiber4Prefix57 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 2) hparentBefore ttFiber4ReverseSingleStep58

theorem ttFiber4State58_in_pass1_full :
    ttFiber4StateAt 58 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix58 ++ [ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix58 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 58) ttFiber4State58_in_pass1_prefix58

theorem ttFiber4State59_in_pass1_prefix59 :
    ttFiber4StateAt 59 ∈ chainClosureStep ttWord ttFiber4Prefix59 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 3 ∈
      chainClosureStep ttWord ttFiber4Prefix58 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix58 = ttFiber4Prefix3 ++ [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 4, ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58]
      (chainClosureStep ttWord ttFiber4Prefix3 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 3) ttFiber4State3_in_pass1_prefix3
  rw [show ttFiber4Prefix59 = ttFiber4Prefix58 ++ [ttFiber4StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 59) []
    (chainClosureStep ttWord ttFiber4Prefix58 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 3) hparentBefore ttFiber4ReverseSingleStep59

theorem ttFiber4State59_in_pass1_full :
    ttFiber4StateAt 59 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix59 ++ [ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix59 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 59) ttFiber4State59_in_pass1_prefix59

theorem ttFiber4State60_in_pass1_prefix60 :
    ttFiber4StateAt 60 ∈ chainClosureStep ttWord ttFiber4Prefix60 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 4 ∈
      chainClosureStep ttWord ttFiber4Prefix59 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix59 = ttFiber4Prefix4 ++ [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 5, ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59]
      (chainClosureStep ttWord ttFiber4Prefix4 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 4) ttFiber4State4_in_pass1_prefix4
  rw [show ttFiber4Prefix60 = ttFiber4Prefix59 ++ [ttFiber4StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 60) []
    (chainClosureStep ttWord ttFiber4Prefix59 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 4) hparentBefore ttFiber4ReverseSingleStep60

theorem ttFiber4State60_in_pass1_full :
    ttFiber4StateAt 60 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix60 ++ [ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix60 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 60) ttFiber4State60_in_pass1_prefix60

theorem ttFiber4State62_in_pass1_prefix62 :
    ttFiber4StateAt 62 ∈ chainClosureStep ttWord ttFiber4Prefix62 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 6 ∈
      chainClosureStep ttWord ttFiber4Prefix61 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix61 = ttFiber4Prefix6 ++ [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61]
      (chainClosureStep ttWord ttFiber4Prefix6 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 6) ttFiber4State6_in_pass1_prefix6
  rw [show ttFiber4Prefix62 = ttFiber4Prefix61 ++ [ttFiber4StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 62) []
    (chainClosureStep ttWord ttFiber4Prefix61 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 6) hparentBefore ttFiber4ReverseSingleStep62

theorem ttFiber4State62_in_pass1_full :
    ttFiber4StateAt 62 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix62 ++ [ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix62 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 62) ttFiber4State62_in_pass1_prefix62

theorem ttFiber4State63_in_pass1_prefix63 :
    ttFiber4StateAt 63 ∈ chainClosureStep ttWord ttFiber4Prefix63 ([ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 7 ∈
      chainClosureStep ttWord ttFiber4Prefix62 ([ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix62 = ttFiber4Prefix7 ++ [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62]
      (chainClosureStep ttWord ttFiber4Prefix7 ([ttFiber4StateAt 0]))
      (ttFiber4StateAt 7) ttFiber4State7_in_pass1_prefix7
  rw [show ttFiber4Prefix63 = ttFiber4Prefix62 ++ [ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 63) []
    (chainClosureStep ttWord ttFiber4Prefix62 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 7) hparentBefore ttFiber4ReverseSingleStep63

theorem ttFiber4State63_in_pass1_full :
    ttFiber4StateAt 63 ∈ chainClosureStep ttWord ttFiber4DirectStates ([ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber4Prefix63 ([ttFiber4StateAt 0]))
    (ttFiber4StateAt 63) ttFiber4State63_in_pass1_prefix63

theorem ttFiber4State5_in_pass2_prefix5 :
    ttFiber4StateAt 5 ∈ chainClosureStep ttWord ttFiber4Prefix5 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 7 ∈
      chainClosureStep ttWord ttFiber4Prefix4 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix4
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 7) ttFiber4State7_in_pass1_full
  rw [show ttFiber4Prefix5 = ttFiber4Prefix4 ++ [ttFiber4StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 5) []
    (chainClosureStep ttWord ttFiber4Prefix4 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 7) hparentBefore ttFiber4ReverseSingleStep5

theorem ttFiber4State5_in_pass2_full :
    ttFiber4StateAt 5 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix5 ++ [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix5 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 5) ttFiber4State5_in_pass2_prefix5

theorem ttFiber4State13_in_pass2_prefix13 :
    ttFiber4StateAt 13 ∈ chainClosureStep ttWord ttFiber4Prefix13 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 5 ∈
      chainClosureStep ttWord ttFiber4Prefix12 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix12 = ttFiber4Prefix5 ++ [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12]
      (chainClosureStep ttWord ttFiber4Prefix5 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 5) ttFiber4State5_in_pass2_prefix5
  rw [show ttFiber4Prefix13 = ttFiber4Prefix12 ++ [ttFiber4StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 13) []
    (chainClosureStep ttWord ttFiber4Prefix12 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 5) hparentBefore ttFiber4ReverseSingleStep13

theorem ttFiber4State13_in_pass2_full :
    ttFiber4StateAt 13 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix13 ++ [ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix13 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 13) ttFiber4State13_in_pass2_prefix13

theorem ttFiber4State32_in_pass2_prefix32 :
    ttFiber4StateAt 32 ∈ chainClosureStep ttWord ttFiber4Prefix32 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 48 ∈
      chainClosureStep ttWord ttFiber4Prefix31 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix31
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 48) ttFiber4State48_in_pass1_full
  rw [show ttFiber4Prefix32 = ttFiber4Prefix31 ++ [ttFiber4StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 32) []
    (chainClosureStep ttWord ttFiber4Prefix31 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 48) hparentBefore ttFiber4ReverseSingleStep32

theorem ttFiber4State32_in_pass2_full :
    ttFiber4StateAt 32 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix32 ++ [ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix32 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 32) ttFiber4State32_in_pass2_prefix32

theorem ttFiber4State33_in_pass2_prefix33 :
    ttFiber4StateAt 33 ∈ chainClosureStep ttWord ttFiber4Prefix33 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 49 ∈
      chainClosureStep ttWord ttFiber4Prefix32 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix32
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 49) ttFiber4State49_in_pass1_full
  rw [show ttFiber4Prefix33 = ttFiber4Prefix32 ++ [ttFiber4StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 33) []
    (chainClosureStep ttWord ttFiber4Prefix32 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 49) hparentBefore ttFiber4ReverseSingleStep33

theorem ttFiber4State33_in_pass2_full :
    ttFiber4StateAt 33 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix33 ++ [ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix33 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 33) ttFiber4State33_in_pass2_prefix33

theorem ttFiber4State37_in_pass2_prefix37 :
    ttFiber4StateAt 37 ∈ chainClosureStep ttWord ttFiber4Prefix37 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 39 ∈
      chainClosureStep ttWord ttFiber4Prefix36 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix36
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 39) ttFiber4State39_in_pass1_full
  rw [show ttFiber4Prefix37 = ttFiber4Prefix36 ++ [ttFiber4StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 37) []
    (chainClosureStep ttWord ttFiber4Prefix36 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 39) hparentBefore ttFiber4ReverseSingleStep37

theorem ttFiber4State37_in_pass2_full :
    ttFiber4StateAt 37 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix37 ++ [ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix37 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 37) ttFiber4State37_in_pass2_prefix37

theorem ttFiber4State40_in_pass2_prefix40 :
    ttFiber4StateAt 40 ∈ chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 56 ∈
      chainClosureStep ttWord ttFiber4Prefix39 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix39
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 56) ttFiber4State56_in_pass1_full
  rw [show ttFiber4Prefix40 = ttFiber4Prefix39 ++ [ttFiber4StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 40) []
    (chainClosureStep ttWord ttFiber4Prefix39 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 56) hparentBefore ttFiber4ReverseSingleStep40

theorem ttFiber4State40_in_pass2_full :
    ttFiber4StateAt 40 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix40 ++ [ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 40) ttFiber4State40_in_pass2_prefix40

theorem ttFiber4State41_in_pass2_prefix41 :
    ttFiber4StateAt 41 ∈ chainClosureStep ttWord ttFiber4Prefix41 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 57 ∈
      chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix40
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 57) ttFiber4State57_in_pass1_full
  rw [show ttFiber4Prefix41 = ttFiber4Prefix40 ++ [ttFiber4StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 41) []
    (chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 57) hparentBefore ttFiber4ReverseSingleStep41

theorem ttFiber4State41_in_pass2_full :
    ttFiber4StateAt 41 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix41 ++ [ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix41 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 41) ttFiber4State41_in_pass2_prefix41

theorem ttFiber4State42_in_pass2_prefix42 :
    ttFiber4StateAt 42 ∈ chainClosureStep ttWord ttFiber4Prefix42 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 58 ∈
      chainClosureStep ttWord ttFiber4Prefix41 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix41
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 58) ttFiber4State58_in_pass1_full
  rw [show ttFiber4Prefix42 = ttFiber4Prefix41 ++ [ttFiber4StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 42) []
    (chainClosureStep ttWord ttFiber4Prefix41 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 58) hparentBefore ttFiber4ReverseSingleStep42

theorem ttFiber4State42_in_pass2_full :
    ttFiber4StateAt 42 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix42 ++ [ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix42 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 42) ttFiber4State42_in_pass2_prefix42

theorem ttFiber4State43_in_pass2_prefix43 :
    ttFiber4StateAt 43 ∈ chainClosureStep ttWord ttFiber4Prefix43 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 40 ∈
      chainClosureStep ttWord ttFiber4Prefix42 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix42 = ttFiber4Prefix40 ++ [ttFiber4StateAt 41, ttFiber4StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 41, ttFiber4StateAt 42]
      (chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 40) ttFiber4State40_in_pass2_prefix40
  rw [show ttFiber4Prefix43 = ttFiber4Prefix42 ++ [ttFiber4StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 43) []
    (chainClosureStep ttWord ttFiber4Prefix42 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 40) hparentBefore ttFiber4ReverseSingleStep43

theorem ttFiber4State43_in_pass2_full :
    ttFiber4StateAt 43 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix43 ++ [ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix43 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 43) ttFiber4State43_in_pass2_prefix43

theorem ttFiber4State44_in_pass2_prefix44 :
    ttFiber4StateAt 44 ∈ chainClosureStep ttWord ttFiber4Prefix44 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 40 ∈
      chainClosureStep ttWord ttFiber4Prefix43 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix43 = ttFiber4Prefix40 ++ [ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43]
      (chainClosureStep ttWord ttFiber4Prefix40 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 40) ttFiber4State40_in_pass2_prefix40
  rw [show ttFiber4Prefix44 = ttFiber4Prefix43 ++ [ttFiber4StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 44) []
    (chainClosureStep ttWord ttFiber4Prefix43 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 40) hparentBefore ttFiber4ReverseSingleStep44

theorem ttFiber4State44_in_pass2_full :
    ttFiber4StateAt 44 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix44 ++ [ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix44 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 44) ttFiber4State44_in_pass2_prefix44

theorem ttFiber4State45_in_pass2_prefix45 :
    ttFiber4StateAt 45 ∈ chainClosureStep ttWord ttFiber4Prefix45 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 41 ∈
      chainClosureStep ttWord ttFiber4Prefix44 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix44 = ttFiber4Prefix41 ++ [ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44]
      (chainClosureStep ttWord ttFiber4Prefix41 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 41) ttFiber4State41_in_pass2_prefix41
  rw [show ttFiber4Prefix45 = ttFiber4Prefix44 ++ [ttFiber4StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 45) []
    (chainClosureStep ttWord ttFiber4Prefix44 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 41) hparentBefore ttFiber4ReverseSingleStep45

theorem ttFiber4State45_in_pass2_full :
    ttFiber4StateAt 45 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix45 ++ [ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix45 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 45) ttFiber4State45_in_pass2_prefix45

theorem ttFiber4State46_in_pass2_prefix46 :
    ttFiber4StateAt 46 ∈ chainClosureStep ttWord ttFiber4Prefix46 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 62 ∈
      chainClosureStep ttWord ttFiber4Prefix45 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix45
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 62) ttFiber4State62_in_pass1_full
  rw [show ttFiber4Prefix46 = ttFiber4Prefix45 ++ [ttFiber4StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 46) []
    (chainClosureStep ttWord ttFiber4Prefix45 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 62) hparentBefore ttFiber4ReverseSingleStep46

theorem ttFiber4State46_in_pass2_full :
    ttFiber4StateAt 46 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix46 ++ [ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix46 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 46) ttFiber4State46_in_pass2_prefix46

theorem ttFiber4State47_in_pass2_prefix47 :
    ttFiber4StateAt 47 ∈ chainClosureStep ttWord ttFiber4Prefix47 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 63 ∈
      chainClosureStep ttWord ttFiber4Prefix46 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber4Prefix46
      (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) (ttFiber4StateAt 63) ttFiber4State63_in_pass1_full
  rw [show ttFiber4Prefix47 = ttFiber4Prefix46 ++ [ttFiber4StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 47) []
    (chainClosureStep ttWord ttFiber4Prefix46 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 63) hparentBefore ttFiber4ReverseSingleStep47

theorem ttFiber4State47_in_pass2_full :
    ttFiber4StateAt 47 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix47 ++ [ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix47 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 47) ttFiber4State47_in_pass2_prefix47

theorem ttFiber4State53_in_pass2_prefix53 :
    ttFiber4StateAt 53 ∈ chainClosureStep ttWord ttFiber4Prefix53 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 13 ∈
      chainClosureStep ttWord ttFiber4Prefix52 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix52 = ttFiber4Prefix13 ++ [ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52]
      (chainClosureStep ttWord ttFiber4Prefix13 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 13) ttFiber4State13_in_pass2_prefix13
  rw [show ttFiber4Prefix53 = ttFiber4Prefix52 ++ [ttFiber4StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 53) []
    (chainClosureStep ttWord ttFiber4Prefix52 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 13) hparentBefore ttFiber4ReverseSingleStep53

theorem ttFiber4State53_in_pass2_full :
    ttFiber4StateAt 53 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix53 ++ [ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60, ttFiber4StateAt 61, ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix53 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 53) ttFiber4State53_in_pass2_prefix53

theorem ttFiber4State61_in_pass2_prefix61 :
    ttFiber4StateAt 61 ∈ chainClosureStep ttWord ttFiber4Prefix61 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  have hparentBefore : ttFiber4StateAt 5 ∈
      chainClosureStep ttWord ttFiber4Prefix60 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
    rw [show ttFiber4Prefix60 = ttFiber4Prefix5 ++ [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 6, ttFiber4StateAt 7, ttFiber4StateAt 8, ttFiber4StateAt 9, ttFiber4StateAt 10, ttFiber4StateAt 11, ttFiber4StateAt 12, ttFiber4StateAt 13, ttFiber4StateAt 14, ttFiber4StateAt 15, ttFiber4StateAt 16, ttFiber4StateAt 17, ttFiber4StateAt 18, ttFiber4StateAt 19, ttFiber4StateAt 20, ttFiber4StateAt 21, ttFiber4StateAt 22, ttFiber4StateAt 23, ttFiber4StateAt 24, ttFiber4StateAt 25, ttFiber4StateAt 26, ttFiber4StateAt 27, ttFiber4StateAt 28, ttFiber4StateAt 29, ttFiber4StateAt 30, ttFiber4StateAt 31, ttFiber4StateAt 32, ttFiber4StateAt 33, ttFiber4StateAt 34, ttFiber4StateAt 35, ttFiber4StateAt 36, ttFiber4StateAt 37, ttFiber4StateAt 38, ttFiber4StateAt 39, ttFiber4StateAt 40, ttFiber4StateAt 41, ttFiber4StateAt 42, ttFiber4StateAt 43, ttFiber4StateAt 44, ttFiber4StateAt 45, ttFiber4StateAt 46, ttFiber4StateAt 47, ttFiber4StateAt 48, ttFiber4StateAt 49, ttFiber4StateAt 50, ttFiber4StateAt 51, ttFiber4StateAt 52, ttFiber4StateAt 53, ttFiber4StateAt 54, ttFiber4StateAt 55, ttFiber4StateAt 56, ttFiber4StateAt 57, ttFiber4StateAt 58, ttFiber4StateAt 59, ttFiber4StateAt 60]
      (chainClosureStep ttWord ttFiber4Prefix5 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
      (ttFiber4StateAt 5) ttFiber4State5_in_pass2_prefix5
  rw [show ttFiber4Prefix61 = ttFiber4Prefix60 ++ [ttFiber4StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber4StateAt 61) []
    (chainClosureStep ttWord ttFiber4Prefix60 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 5) hparentBefore ttFiber4ReverseSingleStep61

theorem ttFiber4State61_in_pass2_full :
    ttFiber4StateAt 61 ∈ chainClosureStep ttWord ttFiber4DirectStates (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]) := by
  rw [show ttFiber4DirectStates = ttFiber4Prefix61 ++ [ttFiber4StateAt 62, ttFiber4StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber4StateAt 62, ttFiber4StateAt 63]
    (chainClosureStep ttWord ttFiber4Prefix61 (chainClosureStep ttWord ttFiber4DirectStates [ttFiber4StateAt 0]))
    (ttFiber4StateAt 61) ttFiber4State61_in_pass2_prefix61

theorem ttFiber4State0_in_close :
    ttFiber4StateAt 0 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber4DirectStates
    ttFiber4DirectStates.length [ttFiber4StateAt 0] (ttFiber4StateAt 0) (by simp)

theorem ttFiber4State1_in_close :
    ttFiber4StateAt 1 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 1 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 1) ttFiber4State1_in_pass1_full

theorem ttFiber4State2_in_close :
    ttFiber4StateAt 2 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 2 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 2) ttFiber4State2_in_pass1_full

theorem ttFiber4State3_in_close :
    ttFiber4StateAt 3 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 3 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 3) ttFiber4State3_in_pass1_full

theorem ttFiber4State4_in_close :
    ttFiber4StateAt 4 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 4 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 4) ttFiber4State4_in_pass1_full

theorem ttFiber4State5_in_close :
    ttFiber4StateAt 5 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 5 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 5) ttFiber4FirstPassGrows
    ttFiber4State5_in_pass2_full

theorem ttFiber4State6_in_close :
    ttFiber4StateAt 6 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 6 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 6) ttFiber4State6_in_pass1_full

theorem ttFiber4State7_in_close :
    ttFiber4StateAt 7 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 7 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 7) ttFiber4State7_in_pass1_full

theorem ttFiber4State8_in_close :
    ttFiber4StateAt 8 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 8 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 8) ttFiber4State8_in_pass1_full

theorem ttFiber4State9_in_close :
    ttFiber4StateAt 9 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 9 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 9) ttFiber4State9_in_pass1_full

theorem ttFiber4State10_in_close :
    ttFiber4StateAt 10 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 10 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 10) ttFiber4State10_in_pass1_full

theorem ttFiber4State11_in_close :
    ttFiber4StateAt 11 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 11 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 11) ttFiber4State11_in_pass1_full

theorem ttFiber4State12_in_close :
    ttFiber4StateAt 12 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 12 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 12) ttFiber4State12_in_pass1_full

theorem ttFiber4State13_in_close :
    ttFiber4StateAt 13 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 13 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 13) ttFiber4FirstPassGrows
    ttFiber4State13_in_pass2_full

theorem ttFiber4State14_in_close :
    ttFiber4StateAt 14 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 14 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 14) ttFiber4State14_in_pass1_full

theorem ttFiber4State15_in_close :
    ttFiber4StateAt 15 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 15 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 15) ttFiber4State15_in_pass1_full

theorem ttFiber4State16_in_close :
    ttFiber4StateAt 16 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 16 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 16) ttFiber4State16_in_pass1_full

theorem ttFiber4State17_in_close :
    ttFiber4StateAt 17 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 17 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 17) ttFiber4State17_in_pass1_full

theorem ttFiber4State18_in_close :
    ttFiber4StateAt 18 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 18 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 18) ttFiber4State18_in_pass1_full

theorem ttFiber4State19_in_close :
    ttFiber4StateAt 19 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 19 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 19) ttFiber4State19_in_pass1_full

theorem ttFiber4State20_in_close :
    ttFiber4StateAt 20 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 20 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 20) ttFiber4State20_in_pass1_full

theorem ttFiber4State21_in_close :
    ttFiber4StateAt 21 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 21 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 21) ttFiber4State21_in_pass1_full

theorem ttFiber4State22_in_close :
    ttFiber4StateAt 22 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 22 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 22) ttFiber4State22_in_pass1_full

theorem ttFiber4State23_in_close :
    ttFiber4StateAt 23 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 23 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 23) ttFiber4State23_in_pass1_full

theorem ttFiber4State24_in_close :
    ttFiber4StateAt 24 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 24 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 24) ttFiber4State24_in_pass1_full

theorem ttFiber4State25_in_close :
    ttFiber4StateAt 25 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 25 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 25) ttFiber4State25_in_pass1_full

theorem ttFiber4State26_in_close :
    ttFiber4StateAt 26 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 26 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 26) ttFiber4State26_in_pass1_full

theorem ttFiber4State27_in_close :
    ttFiber4StateAt 27 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 27 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 27) ttFiber4State27_in_pass1_full

theorem ttFiber4State28_in_close :
    ttFiber4StateAt 28 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 28 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 28) ttFiber4State28_in_pass1_full

theorem ttFiber4State29_in_close :
    ttFiber4StateAt 29 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 29 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 29) ttFiber4State29_in_pass1_full

theorem ttFiber4State30_in_close :
    ttFiber4StateAt 30 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 30 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 30) ttFiber4State30_in_pass1_full

theorem ttFiber4State31_in_close :
    ttFiber4StateAt 31 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 31 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 31) ttFiber4State31_in_pass1_full

theorem ttFiber4State32_in_close :
    ttFiber4StateAt 32 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 32 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 32) ttFiber4FirstPassGrows
    ttFiber4State32_in_pass2_full

theorem ttFiber4State33_in_close :
    ttFiber4StateAt 33 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 33 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 33) ttFiber4FirstPassGrows
    ttFiber4State33_in_pass2_full

theorem ttFiber4State34_in_close :
    ttFiber4StateAt 34 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 34 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 34) ttFiber4State34_in_pass1_full

theorem ttFiber4State35_in_close :
    ttFiber4StateAt 35 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 35 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 35) ttFiber4State35_in_pass1_full

theorem ttFiber4State36_in_close :
    ttFiber4StateAt 36 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 36 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 36) ttFiber4State36_in_pass1_full

theorem ttFiber4State37_in_close :
    ttFiber4StateAt 37 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 37 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 37) ttFiber4FirstPassGrows
    ttFiber4State37_in_pass2_full

theorem ttFiber4State38_in_close :
    ttFiber4StateAt 38 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 38 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 38) ttFiber4State38_in_pass1_full

theorem ttFiber4State39_in_close :
    ttFiber4StateAt 39 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 39 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 39) ttFiber4State39_in_pass1_full

theorem ttFiber4State40_in_close :
    ttFiber4StateAt 40 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 40 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 40) ttFiber4FirstPassGrows
    ttFiber4State40_in_pass2_full

theorem ttFiber4State41_in_close :
    ttFiber4StateAt 41 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 41 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 41) ttFiber4FirstPassGrows
    ttFiber4State41_in_pass2_full

theorem ttFiber4State42_in_close :
    ttFiber4StateAt 42 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 42 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 42) ttFiber4FirstPassGrows
    ttFiber4State42_in_pass2_full

theorem ttFiber4State43_in_close :
    ttFiber4StateAt 43 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 43 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 43) ttFiber4FirstPassGrows
    ttFiber4State43_in_pass2_full

theorem ttFiber4State44_in_close :
    ttFiber4StateAt 44 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 44 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 44) ttFiber4FirstPassGrows
    ttFiber4State44_in_pass2_full

theorem ttFiber4State45_in_close :
    ttFiber4StateAt 45 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 45 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 45) ttFiber4FirstPassGrows
    ttFiber4State45_in_pass2_full

theorem ttFiber4State46_in_close :
    ttFiber4StateAt 46 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 46 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 46) ttFiber4FirstPassGrows
    ttFiber4State46_in_pass2_full

theorem ttFiber4State47_in_close :
    ttFiber4StateAt 47 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 47 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 47) ttFiber4FirstPassGrows
    ttFiber4State47_in_pass2_full

theorem ttFiber4State48_in_close :
    ttFiber4StateAt 48 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 48 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 48) ttFiber4State48_in_pass1_full

theorem ttFiber4State49_in_close :
    ttFiber4StateAt 49 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 49 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 49) ttFiber4State49_in_pass1_full

theorem ttFiber4State50_in_close :
    ttFiber4StateAt 50 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 50 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 50) ttFiber4State50_in_pass1_full

theorem ttFiber4State51_in_close :
    ttFiber4StateAt 51 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 51 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 51) ttFiber4State51_in_pass1_full

theorem ttFiber4State52_in_close :
    ttFiber4StateAt 52 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 52 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 52) ttFiber4State52_in_pass1_full

theorem ttFiber4State53_in_close :
    ttFiber4StateAt 53 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 53 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 53) ttFiber4FirstPassGrows
    ttFiber4State53_in_pass2_full

theorem ttFiber4State54_in_close :
    ttFiber4StateAt 54 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 54 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 54) ttFiber4State54_in_pass1_full

theorem ttFiber4State55_in_close :
    ttFiber4StateAt 55 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 55 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 55) ttFiber4State55_in_pass1_full

theorem ttFiber4State56_in_close :
    ttFiber4StateAt 56 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 56 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 56) ttFiber4State56_in_pass1_full

theorem ttFiber4State57_in_close :
    ttFiber4StateAt 57 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 57 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 57) ttFiber4State57_in_pass1_full

theorem ttFiber4State58_in_close :
    ttFiber4StateAt 58 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 58 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 58) ttFiber4State58_in_pass1_full

theorem ttFiber4State59_in_close :
    ttFiber4StateAt 59 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 59 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 59) ttFiber4State59_in_pass1_full

theorem ttFiber4State60_in_close :
    ttFiber4StateAt 60 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 60 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 60) ttFiber4State60_in_pass1_full

theorem ttFiber4State61_in_close :
    ttFiber4StateAt 61 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 61 ∈ closeChainFiber ttWord ttFiber4DirectStates (62 + 2)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber4DirectStates 62
    [ttFiber4StateAt 0] (ttFiber4StateAt 61) ttFiber4FirstPassGrows
    ttFiber4State61_in_pass2_full

theorem ttFiber4State62_in_close :
    ttFiber4StateAt 62 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 62 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 62) ttFiber4State62_in_pass1_full

theorem ttFiber4State63_in_close :
    ttFiber4StateAt 63 ∈
      closeChainFiber ttWord ttFiber4DirectStates ttFiber4DirectStates.length
        [ttFiber4StateAt 0] := by
  change ttFiber4StateAt 63 ∈ closeChainFiber ttWord ttFiber4DirectStates (63 + 1)
    [ttFiber4StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber4DirectStates 63
    [ttFiber4StateAt 0] (ttFiber4StateAt 63) ttFiber4State63_in_pass1_full

theorem ttFiber4DirectConnected :
    chainFiberConnected ttWord ttFiber4DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber4DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber4State0_in_close
  · subst state
    exact ttFiber4State1_in_close
  · subst state
    exact ttFiber4State2_in_close
  · subst state
    exact ttFiber4State3_in_close
  · subst state
    exact ttFiber4State4_in_close
  · subst state
    exact ttFiber4State5_in_close
  · subst state
    exact ttFiber4State6_in_close
  · subst state
    exact ttFiber4State7_in_close
  · subst state
    exact ttFiber4State8_in_close
  · subst state
    exact ttFiber4State9_in_close
  · subst state
    exact ttFiber4State10_in_close
  · subst state
    exact ttFiber4State11_in_close
  · subst state
    exact ttFiber4State12_in_close
  · subst state
    exact ttFiber4State13_in_close
  · subst state
    exact ttFiber4State14_in_close
  · subst state
    exact ttFiber4State15_in_close
  · subst state
    exact ttFiber4State16_in_close
  · subst state
    exact ttFiber4State17_in_close
  · subst state
    exact ttFiber4State18_in_close
  · subst state
    exact ttFiber4State19_in_close
  · subst state
    exact ttFiber4State20_in_close
  · subst state
    exact ttFiber4State21_in_close
  · subst state
    exact ttFiber4State22_in_close
  · subst state
    exact ttFiber4State23_in_close
  · subst state
    exact ttFiber4State24_in_close
  · subst state
    exact ttFiber4State25_in_close
  · subst state
    exact ttFiber4State26_in_close
  · subst state
    exact ttFiber4State27_in_close
  · subst state
    exact ttFiber4State28_in_close
  · subst state
    exact ttFiber4State29_in_close
  · subst state
    exact ttFiber4State30_in_close
  · subst state
    exact ttFiber4State31_in_close
  · subst state
    exact ttFiber4State32_in_close
  · subst state
    exact ttFiber4State33_in_close
  · subst state
    exact ttFiber4State34_in_close
  · subst state
    exact ttFiber4State35_in_close
  · subst state
    exact ttFiber4State36_in_close
  · subst state
    exact ttFiber4State37_in_close
  · subst state
    exact ttFiber4State38_in_close
  · subst state
    exact ttFiber4State39_in_close
  · subst state
    exact ttFiber4State40_in_close
  · subst state
    exact ttFiber4State41_in_close
  · subst state
    exact ttFiber4State42_in_close
  · subst state
    exact ttFiber4State43_in_close
  · subst state
    exact ttFiber4State44_in_close
  · subst state
    exact ttFiber4State45_in_close
  · subst state
    exact ttFiber4State46_in_close
  · subst state
    exact ttFiber4State47_in_close
  · subst state
    exact ttFiber4State48_in_close
  · subst state
    exact ttFiber4State49_in_close
  · subst state
    exact ttFiber4State50_in_close
  · subst state
    exact ttFiber4State51_in_close
  · subst state
    exact ttFiber4State52_in_close
  · subst state
    exact ttFiber4State53_in_close
  · subst state
    exact ttFiber4State54_in_close
  · subst state
    exact ttFiber4State55_in_close
  · subst state
    exact ttFiber4State56_in_close
  · subst state
    exact ttFiber4State57_in_close
  · subst state
    exact ttFiber4State58_in_close
  · subst state
    exact ttFiber4State59_in_close
  · subst state
    exact ttFiber4State60_in_close
  · subst state
    exact ttFiber4State61_in_close
  · subst state
    exact ttFiber4State62_in_close
  · subst state
    exact ttFiber4State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
