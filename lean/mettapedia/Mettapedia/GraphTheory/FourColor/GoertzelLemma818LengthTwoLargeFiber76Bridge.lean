import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype multi-pass direct closure bridge for generated length-two fiber ttFiber76

This module checks the proof shape for a generated `tau,tau` fiber whose
parent order requires two closure scans.  It remains a local bridge
prototype, not the final real `chainLKRInAudit` theorem.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber76StateAt (i : Nat) : List TauState :=
  directStates (ttFiber76RowAt i).sourceLeft (ttFiber76RowAt i).sourceRight

def ttFiber76DirectStates : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]

def ttFiber76Prefix0 : List (List TauState) :=
  [ttFiber76StateAt 0]

def ttFiber76Prefix1 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1]

def ttFiber76Prefix2 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2]

def ttFiber76Prefix3 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3]

def ttFiber76Prefix4 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4]

def ttFiber76Prefix5 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5]

def ttFiber76Prefix6 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6]

def ttFiber76Prefix7 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7]

def ttFiber76Prefix8 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8]

def ttFiber76Prefix9 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9]

def ttFiber76Prefix10 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10]

def ttFiber76Prefix11 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11]

def ttFiber76Prefix12 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12]

def ttFiber76Prefix13 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13]

def ttFiber76Prefix14 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14]

def ttFiber76Prefix15 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15]

def ttFiber76Prefix16 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16]

def ttFiber76Prefix17 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17]

def ttFiber76Prefix18 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18]

def ttFiber76Prefix19 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19]

def ttFiber76Prefix20 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20]

def ttFiber76Prefix21 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21]

def ttFiber76Prefix22 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22]

def ttFiber76Prefix23 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23]

def ttFiber76Prefix24 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24]

def ttFiber76Prefix25 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25]

def ttFiber76Prefix26 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26]

def ttFiber76Prefix27 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27]

def ttFiber76Prefix28 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28]

def ttFiber76Prefix29 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29]

def ttFiber76Prefix30 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30]

def ttFiber76Prefix31 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31]

def ttFiber76Prefix32 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32]

def ttFiber76Prefix33 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33]

def ttFiber76Prefix34 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34]

def ttFiber76Prefix35 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35]

def ttFiber76Prefix36 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36]

def ttFiber76Prefix37 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37]

def ttFiber76Prefix38 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38]

def ttFiber76Prefix39 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39]

def ttFiber76Prefix40 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40]

def ttFiber76Prefix41 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41]

def ttFiber76Prefix42 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42]

def ttFiber76Prefix43 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43]

def ttFiber76Prefix44 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44]

def ttFiber76Prefix45 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45]

def ttFiber76Prefix46 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46]

def ttFiber76Prefix47 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47]

def ttFiber76Prefix48 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48]

def ttFiber76Prefix49 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49]

def ttFiber76Prefix50 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50]

def ttFiber76Prefix51 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51]

def ttFiber76Prefix52 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52]

def ttFiber76Prefix53 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53]

def ttFiber76Prefix54 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54]

def ttFiber76Prefix55 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55]

def ttFiber76Prefix56 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56]

def ttFiber76Prefix57 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57]

def ttFiber76Prefix58 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58]

def ttFiber76Prefix59 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59]

def ttFiber76Prefix60 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60]

def ttFiber76Prefix61 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61]

def ttFiber76Prefix62 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62]

def ttFiber76Prefix63 : List (List TauState) :=
  [ttFiber76StateAt 0, ttFiber76StateAt 1, ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]

theorem ttFiber76ReverseRow_1_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk0] at h
  exact h.2

theorem ttFiber76ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 1)
      (ttFiber76RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 1) (by decide) ttFiber76ReverseRow_1_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_2_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk1] at h
  exact h.1

theorem ttFiber76ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 2)
      (ttFiber76RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 2) (by decide) ttFiber76ReverseRow_2_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_3_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk1] at h
  exact h.2

theorem ttFiber76ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 3)
      (ttFiber76RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 3) (by decide) ttFiber76ReverseRow_3_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_4_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk2] at h
  exact h.1

theorem ttFiber76ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 4)
      (ttFiber76RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 4) (by decide) ttFiber76ReverseRow_4_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_5_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk2] at h
  exact h.2

theorem ttFiber76ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 5)
      (ttFiber76RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 5) (by decide) ttFiber76ReverseRow_5_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_6_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk3] at h
  exact h.1

theorem ttFiber76ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 6)
      (ttFiber76RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 6) (by decide) ttFiber76ReverseRow_6_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_7_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk3] at h
  exact h.2

theorem ttFiber76ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 7)
      (ttFiber76RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 7) (by decide) ttFiber76ReverseRow_7_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_8_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk4] at h
  exact h.1

theorem ttFiber76ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 8)
      (ttFiber76RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 8) (by decide) ttFiber76ReverseRow_8_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_9_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk4] at h
  exact h.2

theorem ttFiber76ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 9)
      (ttFiber76RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 9) (by decide) ttFiber76ReverseRow_9_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_10_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk5] at h
  exact h.1

theorem ttFiber76ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 10)
      (ttFiber76RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 10) (by decide) ttFiber76ReverseRow_10_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_11_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk5] at h
  exact h.2

theorem ttFiber76ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 11)
      (ttFiber76RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 11) (by decide) ttFiber76ReverseRow_11_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_12_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk6] at h
  exact h.1

theorem ttFiber76ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 4) (ttFiber76StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 4) (ttFiber76StateAt 12)
      (ttFiber76RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 12) (by decide) ttFiber76ReverseRow_12_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_13_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk6] at h
  exact h.2

theorem ttFiber76ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 5) (ttFiber76StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 5) (ttFiber76StateAt 13)
      (ttFiber76RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 13) (by decide) ttFiber76ReverseRow_13_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_14_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk7] at h
  exact h.1

theorem ttFiber76ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 14)
      (ttFiber76RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 14) (by decide) ttFiber76ReverseRow_14_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_15_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk7] at h
  exact h.2

theorem ttFiber76ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 15)
      (ttFiber76RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 15) (by decide) ttFiber76ReverseRow_15_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_16_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk8] at h
  exact h.1

theorem ttFiber76ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 16)
      (ttFiber76RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 16) (by decide) ttFiber76ReverseRow_16_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_17_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk8] at h
  exact h.2

theorem ttFiber76ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 17)
      (ttFiber76RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 17) (by decide) ttFiber76ReverseRow_17_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_18_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk9] at h
  exact h.1

theorem ttFiber76ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 18)
      (ttFiber76RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 18) (by decide) ttFiber76ReverseRow_18_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_19_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk9] at h
  exact h.2

theorem ttFiber76ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 19)
      (ttFiber76RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 19) (by decide) ttFiber76ReverseRow_19_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_20_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk10] at h
  exact h.1

theorem ttFiber76ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 16) (ttFiber76StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 16) (ttFiber76StateAt 20)
      (ttFiber76RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 20) (by decide) ttFiber76ReverseRow_20_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_21_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk10] at h
  exact h.2

theorem ttFiber76ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 17) (ttFiber76StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 17) (ttFiber76StateAt 21)
      (ttFiber76RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 21) (by decide) ttFiber76ReverseRow_21_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_22_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk11] at h
  exact h.1

theorem ttFiber76ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 22)
      (ttFiber76RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 22) (by decide) ttFiber76ReverseRow_22_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_23_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk11] at h
  exact h.2

theorem ttFiber76ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 23)
      (ttFiber76RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 23) (by decide) ttFiber76ReverseRow_23_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_24_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk12] at h
  exact h.1

theorem ttFiber76ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 8) (ttFiber76StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 8) (ttFiber76StateAt 24)
      (ttFiber76RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 24) (by decide) ttFiber76ReverseRow_24_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_25_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk12] at h
  exact h.2

theorem ttFiber76ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 9) (ttFiber76StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 9) (ttFiber76StateAt 25)
      (ttFiber76RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 25) (by decide) ttFiber76ReverseRow_25_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_26_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk13] at h
  exact h.1

theorem ttFiber76ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 10) (ttFiber76StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 10) (ttFiber76StateAt 26)
      (ttFiber76RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 26) (by decide) ttFiber76ReverseRow_26_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_27_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk13] at h
  exact h.2

theorem ttFiber76ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 11) (ttFiber76StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 11) (ttFiber76StateAt 27)
      (ttFiber76RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 27) (by decide) ttFiber76ReverseRow_27_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_28_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk14] at h
  exact h.1

theorem ttFiber76ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 24) (ttFiber76StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 24) (ttFiber76StateAt 28)
      (ttFiber76RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 28) (by decide) ttFiber76ReverseRow_28_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_29_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk14] at h
  exact h.2

theorem ttFiber76ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 25) (ttFiber76StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 25) (ttFiber76StateAt 29)
      (ttFiber76RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 29) (by decide) ttFiber76ReverseRow_29_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_30_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk15] at h
  exact h.1

theorem ttFiber76ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 14) (ttFiber76StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 14) (ttFiber76StateAt 30)
      (ttFiber76RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 30) (by decide) ttFiber76ReverseRow_30_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_31_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk15] at h
  exact h.2

theorem ttFiber76ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 15) (ttFiber76StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 15) (ttFiber76StateAt 31)
      (ttFiber76RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 31) (by decide) ttFiber76ReverseRow_31_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_32_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk16] at h
  exact h.1

theorem ttFiber76ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 48) (ttFiber76StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 48) (ttFiber76StateAt 32)
      (ttFiber76RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 32) (by decide) ttFiber76ReverseRow_32_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_33_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk16] at h
  exact h.2

theorem ttFiber76ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 49) (ttFiber76StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 49) (ttFiber76StateAt 33)
      (ttFiber76RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 33) (by decide) ttFiber76ReverseRow_33_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_34_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk17] at h
  exact h.1

theorem ttFiber76ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 22) (ttFiber76StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 22) (ttFiber76StateAt 34)
      (ttFiber76RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 34) (by decide) ttFiber76ReverseRow_34_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_35_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk17] at h
  exact h.2

theorem ttFiber76ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 23) (ttFiber76StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 23) (ttFiber76StateAt 35)
      (ttFiber76RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 35) (by decide) ttFiber76ReverseRow_35_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_36_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk18] at h
  exact h.1

theorem ttFiber76ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 18) (ttFiber76StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 18) (ttFiber76StateAt 36)
      (ttFiber76RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 36) (by decide) ttFiber76ReverseRow_36_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_37_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk18] at h
  exact h.2

theorem ttFiber76ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 39) (ttFiber76StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 39) (ttFiber76StateAt 37)
      (ttFiber76RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 37) (by decide) ttFiber76ReverseRow_37_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_38_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk19] at h
  exact h.1

theorem ttFiber76ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 17) (ttFiber76StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 17) (ttFiber76StateAt 38)
      (ttFiber76RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 38) (by decide) ttFiber76ReverseRow_38_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_39_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk19] at h
  exact h.2

theorem ttFiber76ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 16) (ttFiber76StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 16) (ttFiber76StateAt 39)
      (ttFiber76RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 39) (by decide) ttFiber76ReverseRow_39_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_40_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk20] at h
  exact h.1

theorem ttFiber76ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 56) (ttFiber76StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 56) (ttFiber76StateAt 40)
      (ttFiber76RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 40) (by decide) ttFiber76ReverseRow_40_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_41_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk20] at h
  exact h.2

theorem ttFiber76ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 57) (ttFiber76StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 57) (ttFiber76StateAt 41)
      (ttFiber76RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 41) (by decide) ttFiber76ReverseRow_41_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_42_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk21] at h
  exact h.1

theorem ttFiber76ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 58) (ttFiber76StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 58) (ttFiber76StateAt 42)
      (ttFiber76RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 42) (by decide) ttFiber76ReverseRow_42_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_43_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk21] at h
  exact h.2

theorem ttFiber76ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 40) (ttFiber76StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 40) (ttFiber76StateAt 43)
      (ttFiber76RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 43) (by decide) ttFiber76ReverseRow_43_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_44_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk22] at h
  exact h.1

theorem ttFiber76ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 40) (ttFiber76StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 40) (ttFiber76StateAt 44)
      (ttFiber76RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 44) (by decide) ttFiber76ReverseRow_44_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_45_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk22] at h
  exact h.2

theorem ttFiber76ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 41) (ttFiber76StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 41) (ttFiber76StateAt 45)
      (ttFiber76RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 45) (by decide) ttFiber76ReverseRow_45_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_46_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk23] at h
  exact h.1

theorem ttFiber76ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 62) (ttFiber76StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 62) (ttFiber76StateAt 46)
      (ttFiber76RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 46) (by decide) ttFiber76ReverseRow_46_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_47_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk23] at h
  exact h.2

theorem ttFiber76ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 63) (ttFiber76StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 63) (ttFiber76StateAt 47)
      (ttFiber76RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 47) (by decide) ttFiber76ReverseRow_47_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_48_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk24] at h
  exact h.1

theorem ttFiber76ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 8) (ttFiber76StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 8) (ttFiber76StateAt 48)
      (ttFiber76RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 48) (by decide) ttFiber76ReverseRow_48_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_49_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk24] at h
  exact h.2

theorem ttFiber76ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 9) (ttFiber76StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 9) (ttFiber76StateAt 49)
      (ttFiber76RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 49) (by decide) ttFiber76ReverseRow_49_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_50_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk25] at h
  exact h.1

theorem ttFiber76ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 10) (ttFiber76StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 10) (ttFiber76StateAt 50)
      (ttFiber76RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 50) (by decide) ttFiber76ReverseRow_50_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_51_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk25] at h
  exact h.2

theorem ttFiber76ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 11) (ttFiber76StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 11) (ttFiber76StateAt 51)
      (ttFiber76RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 51) (by decide) ttFiber76ReverseRow_51_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_52_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk26] at h
  exact h.1

theorem ttFiber76ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 12) (ttFiber76StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 12) (ttFiber76StateAt 52)
      (ttFiber76RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 52) (by decide) ttFiber76ReverseRow_52_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_53_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk26] at h
  exact h.2

theorem ttFiber76ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 13) (ttFiber76StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 13) (ttFiber76StateAt 53)
      (ttFiber76RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 53) (by decide) ttFiber76ReverseRow_53_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_54_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk27] at h
  exact h.1

theorem ttFiber76ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 14) (ttFiber76StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 14) (ttFiber76StateAt 54)
      (ttFiber76RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 54) (by decide) ttFiber76ReverseRow_54_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_55_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk27] at h
  exact h.2

theorem ttFiber76ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 15) (ttFiber76StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 15) (ttFiber76StateAt 55)
      (ttFiber76RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 55) (by decide) ttFiber76ReverseRow_55_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_56_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk28] at h
  exact h.1

theorem ttFiber76ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 0) (ttFiber76StateAt 56)
      (ttFiber76RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 56) (by decide) ttFiber76ReverseRow_56_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_57_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk28] at h
  exact h.2

theorem ttFiber76ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 1) (ttFiber76StateAt 57)
      (ttFiber76RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 57) (by decide) ttFiber76ReverseRow_57_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_58_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk29] at h
  exact h.1

theorem ttFiber76ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 2) (ttFiber76StateAt 58)
      (ttFiber76RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 58) (by decide) ttFiber76ReverseRow_58_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_59_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk29] at h
  exact h.2

theorem ttFiber76ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 3) (ttFiber76StateAt 59)
      (ttFiber76RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 59) (by decide) ttFiber76ReverseRow_59_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_60_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk30] at h
  exact h.1

theorem ttFiber76ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 4) (ttFiber76StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 4) (ttFiber76StateAt 60)
      (ttFiber76RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 60) (by decide) ttFiber76ReverseRow_60_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_61_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk30] at h
  exact h.2

theorem ttFiber76ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 5) (ttFiber76StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 5) (ttFiber76StateAt 61)
      (ttFiber76RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 61) (by decide) ttFiber76ReverseRow_61_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_62_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk31] at h
  exact h.1

theorem ttFiber76ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 6) (ttFiber76StateAt 62)
      (ttFiber76RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 62) (by decide) ttFiber76ReverseRow_62_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76ReverseRow_63_ok' :
    directRowReverseValid ttFiber76Key ttFiber76Expected (ttFiber76RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber76Chunk31] at h
  exact h.2

theorem ttFiber76ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber76StateAt 7) (ttFiber76StateAt 63)
      (ttFiber76RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber76Key ttFiber76Expected
      (ttFiber76RowAt 63) (by decide) ttFiber76ReverseRow_63_ok'
    simpa [ttFiber76StateAt, ttFiber76RowAt, ttFiber76Rows, listGetD, directRow] using h

theorem ttFiber76FirstPassGrows :
    ((chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]).length ==
      [ttFiber76StateAt 0].length) = false := by
  have hroot : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber76DirectStates [ttFiber76StateAt 0]
      (ttFiber76StateAt 0) (by simp)
  have hnew : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber76DirectStates [ttFiber76StateAt 0]
      (ttFiber76StateAt 0) (ttFiber76StateAt 1) (by decide) (by simp)
      ttFiber76ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0])
    (ttFiber76StateAt 0) (ttFiber76StateAt 1) hroot hnew (by decide)

theorem ttFiber76State0_in_pass0_full :
    ttFiber76StateAt 0 ∈ [ttFiber76StateAt 0] := by
  simp

theorem ttFiber76State1_in_pass1_prefix1 :
    ttFiber76StateAt 1 ∈ chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix0 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix0
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix1 = ttFiber76Prefix0 ++ [ttFiber76StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 1) []
    (chainClosureStep ttWord ttFiber76Prefix0 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep1

theorem ttFiber76State1_in_pass1_full :
    ttFiber76StateAt 1 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix1 ++ [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1

theorem ttFiber76State2_in_pass1_prefix2 :
    ttFiber76StateAt 2 ∈ chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix1
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix2 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 2) []
    (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep2

theorem ttFiber76State2_in_pass1_full :
    ttFiber76StateAt 2 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix2 ++ [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 2) ttFiber76State2_in_pass1_prefix2

theorem ttFiber76State3_in_pass1_prefix3 :
    ttFiber76StateAt 3 ∈ chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix2 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2]
      (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1
  rw [show ttFiber76Prefix3 = ttFiber76Prefix2 ++ [ttFiber76StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 3) []
    (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) hparentBefore ttFiber76ReverseSingleStep3

theorem ttFiber76State3_in_pass1_full :
    ttFiber76StateAt 3 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix3 ++ [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 3) ttFiber76State3_in_pass1_prefix3

theorem ttFiber76State4_in_pass1_prefix4 :
    ttFiber76StateAt 4 ∈ chainClosureStep ttWord ttFiber76Prefix4 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 2 ∈
      chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix3 = ttFiber76Prefix2 ++ [ttFiber76StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 3]
      (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 2) ttFiber76State2_in_pass1_prefix2
  rw [show ttFiber76Prefix4 = ttFiber76Prefix3 ++ [ttFiber76StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 4) []
    (chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 2) hparentBefore ttFiber76ReverseSingleStep4

theorem ttFiber76State4_in_pass1_full :
    ttFiber76StateAt 4 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix4 ++ [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix4 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 4) ttFiber76State4_in_pass1_prefix4

theorem ttFiber76State6_in_pass1_prefix6 :
    ttFiber76StateAt 6 ∈ chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76Prefix5 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix5 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5]
      (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1
  rw [show ttFiber76Prefix6 = ttFiber76Prefix5 ++ [ttFiber76StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 6) []
    (chainClosureStep ttWord ttFiber76Prefix5 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) hparentBefore ttFiber76ReverseSingleStep6

theorem ttFiber76State6_in_pass1_full :
    ttFiber76StateAt 6 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix6 ++ [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 6) ttFiber76State6_in_pass1_prefix6

theorem ttFiber76State7_in_pass1_prefix7 :
    ttFiber76StateAt 7 ∈ chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix6
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix7 = ttFiber76Prefix6 ++ [ttFiber76StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 7) []
    (chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep7

theorem ttFiber76State7_in_pass1_full :
    ttFiber76StateAt 7 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix7 ++ [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 7) ttFiber76State7_in_pass1_prefix7

theorem ttFiber76State8_in_pass1_prefix8 :
    ttFiber76StateAt 8 ∈ chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix7
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix8 = ttFiber76Prefix7 ++ [ttFiber76StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 8) []
    (chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep8

theorem ttFiber76State8_in_pass1_full :
    ttFiber76StateAt 8 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix8 ++ [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 8) ttFiber76State8_in_pass1_prefix8

theorem ttFiber76State9_in_pass1_prefix9 :
    ttFiber76StateAt 9 ∈ chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix8 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8]
      (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1
  rw [show ttFiber76Prefix9 = ttFiber76Prefix8 ++ [ttFiber76StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 9) []
    (chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) hparentBefore ttFiber76ReverseSingleStep9

theorem ttFiber76State9_in_pass1_full :
    ttFiber76StateAt 9 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix9 ++ [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 9) ttFiber76State9_in_pass1_prefix9

theorem ttFiber76State10_in_pass1_prefix10 :
    ttFiber76StateAt 10 ∈ chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 2 ∈
      chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix9 = ttFiber76Prefix2 ++ [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9]
      (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 2) ttFiber76State2_in_pass1_prefix2
  rw [show ttFiber76Prefix10 = ttFiber76Prefix9 ++ [ttFiber76StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 10) []
    (chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 2) hparentBefore ttFiber76ReverseSingleStep10

theorem ttFiber76State10_in_pass1_full :
    ttFiber76StateAt 10 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix10 ++ [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 10) ttFiber76State10_in_pass1_prefix10

theorem ttFiber76State11_in_pass1_prefix11 :
    ttFiber76StateAt 11 ∈ chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 3 ∈
      chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix10 = ttFiber76Prefix3 ++ [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10]
      (chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 3) ttFiber76State3_in_pass1_prefix3
  rw [show ttFiber76Prefix11 = ttFiber76Prefix10 ++ [ttFiber76StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 11) []
    (chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 3) hparentBefore ttFiber76ReverseSingleStep11

theorem ttFiber76State11_in_pass1_full :
    ttFiber76StateAt 11 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix11 ++ [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 11) ttFiber76State11_in_pass1_prefix11

theorem ttFiber76State12_in_pass1_prefix12 :
    ttFiber76StateAt 12 ∈ chainClosureStep ttWord ttFiber76Prefix12 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 4 ∈
      chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix11 = ttFiber76Prefix4 ++ [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11]
      (chainClosureStep ttWord ttFiber76Prefix4 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 4) ttFiber76State4_in_pass1_prefix4
  rw [show ttFiber76Prefix12 = ttFiber76Prefix11 ++ [ttFiber76StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 12) []
    (chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 4) hparentBefore ttFiber76ReverseSingleStep12

theorem ttFiber76State12_in_pass1_full :
    ttFiber76StateAt 12 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix12 ++ [ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix12 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 12) ttFiber76State12_in_pass1_prefix12

theorem ttFiber76State14_in_pass1_prefix14 :
    ttFiber76StateAt 14 ∈ chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 6 ∈
      chainClosureStep ttWord ttFiber76Prefix13 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix13 = ttFiber76Prefix6 ++ [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13]
      (chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 6) ttFiber76State6_in_pass1_prefix6
  rw [show ttFiber76Prefix14 = ttFiber76Prefix13 ++ [ttFiber76StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 14) []
    (chainClosureStep ttWord ttFiber76Prefix13 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 6) hparentBefore ttFiber76ReverseSingleStep14

theorem ttFiber76State14_in_pass1_full :
    ttFiber76StateAt 14 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix14 ++ [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 14) ttFiber76State14_in_pass1_prefix14

theorem ttFiber76State15_in_pass1_prefix15 :
    ttFiber76StateAt 15 ∈ chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 7 ∈
      chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix14 = ttFiber76Prefix7 ++ [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14]
      (chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 7) ttFiber76State7_in_pass1_prefix7
  rw [show ttFiber76Prefix15 = ttFiber76Prefix14 ++ [ttFiber76StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 15) []
    (chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 7) hparentBefore ttFiber76ReverseSingleStep15

theorem ttFiber76State15_in_pass1_full :
    ttFiber76StateAt 15 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix15 ++ [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 15) ttFiber76State15_in_pass1_prefix15

theorem ttFiber76State16_in_pass1_prefix16 :
    ttFiber76StateAt 16 ∈ chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix15
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix16 = ttFiber76Prefix15 ++ [ttFiber76StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 16) []
    (chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep16

theorem ttFiber76State16_in_pass1_full :
    ttFiber76StateAt 16 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix16 ++ [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 16) ttFiber76State16_in_pass1_prefix16

theorem ttFiber76State17_in_pass1_prefix17 :
    ttFiber76StateAt 17 ∈ chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix16 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16]
      (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1
  rw [show ttFiber76Prefix17 = ttFiber76Prefix16 ++ [ttFiber76StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 17) []
    (chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) hparentBefore ttFiber76ReverseSingleStep17

theorem ttFiber76State17_in_pass1_full :
    ttFiber76StateAt 17 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix17 ++ [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 17) ttFiber76State17_in_pass1_prefix17

theorem ttFiber76State18_in_pass1_prefix18 :
    ttFiber76StateAt 18 ∈ chainClosureStep ttWord ttFiber76Prefix18 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 2 ∈
      chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix17 = ttFiber76Prefix2 ++ [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17]
      (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 2) ttFiber76State2_in_pass1_prefix2
  rw [show ttFiber76Prefix18 = ttFiber76Prefix17 ++ [ttFiber76StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 18) []
    (chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 2) hparentBefore ttFiber76ReverseSingleStep18

theorem ttFiber76State18_in_pass1_full :
    ttFiber76StateAt 18 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix18 ++ [ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix18 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 18) ttFiber76State18_in_pass1_prefix18

theorem ttFiber76State19_in_pass1_prefix19 :
    ttFiber76StateAt 19 ∈ chainClosureStep ttWord ttFiber76Prefix19 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 3 ∈
      chainClosureStep ttWord ttFiber76Prefix18 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix18 = ttFiber76Prefix3 ++ [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18]
      (chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 3) ttFiber76State3_in_pass1_prefix3
  rw [show ttFiber76Prefix19 = ttFiber76Prefix18 ++ [ttFiber76StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 19) []
    (chainClosureStep ttWord ttFiber76Prefix18 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 3) hparentBefore ttFiber76ReverseSingleStep19

theorem ttFiber76State19_in_pass1_full :
    ttFiber76StateAt 19 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix19 ++ [ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix19 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 19) ttFiber76State19_in_pass1_prefix19

theorem ttFiber76State20_in_pass1_prefix20 :
    ttFiber76StateAt 20 ∈ chainClosureStep ttWord ttFiber76Prefix20 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 16 ∈
      chainClosureStep ttWord ttFiber76Prefix19 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix19 = ttFiber76Prefix16 ++ [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19]
      (chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 16) ttFiber76State16_in_pass1_prefix16
  rw [show ttFiber76Prefix20 = ttFiber76Prefix19 ++ [ttFiber76StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 20) []
    (chainClosureStep ttWord ttFiber76Prefix19 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 16) hparentBefore ttFiber76ReverseSingleStep20

theorem ttFiber76State20_in_pass1_full :
    ttFiber76StateAt 20 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix20 ++ [ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix20 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 20) ttFiber76State20_in_pass1_prefix20

theorem ttFiber76State21_in_pass1_prefix21 :
    ttFiber76StateAt 21 ∈ chainClosureStep ttWord ttFiber76Prefix21 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 17 ∈
      chainClosureStep ttWord ttFiber76Prefix20 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix20 = ttFiber76Prefix17 ++ [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20]
      (chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 17) ttFiber76State17_in_pass1_prefix17
  rw [show ttFiber76Prefix21 = ttFiber76Prefix20 ++ [ttFiber76StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 21) []
    (chainClosureStep ttWord ttFiber76Prefix20 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 17) hparentBefore ttFiber76ReverseSingleStep21

theorem ttFiber76State21_in_pass1_full :
    ttFiber76StateAt 21 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix21 ++ [ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix21 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 21) ttFiber76State21_in_pass1_prefix21

theorem ttFiber76State22_in_pass1_prefix22 :
    ttFiber76StateAt 22 ∈ chainClosureStep ttWord ttFiber76Prefix22 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 6 ∈
      chainClosureStep ttWord ttFiber76Prefix21 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix21 = ttFiber76Prefix6 ++ [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21]
      (chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 6) ttFiber76State6_in_pass1_prefix6
  rw [show ttFiber76Prefix22 = ttFiber76Prefix21 ++ [ttFiber76StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 22) []
    (chainClosureStep ttWord ttFiber76Prefix21 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 6) hparentBefore ttFiber76ReverseSingleStep22

theorem ttFiber76State22_in_pass1_full :
    ttFiber76StateAt 22 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix22 ++ [ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix22 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 22) ttFiber76State22_in_pass1_prefix22

theorem ttFiber76State23_in_pass1_prefix23 :
    ttFiber76StateAt 23 ∈ chainClosureStep ttWord ttFiber76Prefix23 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 7 ∈
      chainClosureStep ttWord ttFiber76Prefix22 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix22 = ttFiber76Prefix7 ++ [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22]
      (chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 7) ttFiber76State7_in_pass1_prefix7
  rw [show ttFiber76Prefix23 = ttFiber76Prefix22 ++ [ttFiber76StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 23) []
    (chainClosureStep ttWord ttFiber76Prefix22 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 7) hparentBefore ttFiber76ReverseSingleStep23

theorem ttFiber76State23_in_pass1_full :
    ttFiber76StateAt 23 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix23 ++ [ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix23 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 23) ttFiber76State23_in_pass1_prefix23

theorem ttFiber76State24_in_pass1_prefix24 :
    ttFiber76StateAt 24 ∈ chainClosureStep ttWord ttFiber76Prefix24 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 8 ∈
      chainClosureStep ttWord ttFiber76Prefix23 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix23 = ttFiber76Prefix8 ++ [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23]
      (chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 8) ttFiber76State8_in_pass1_prefix8
  rw [show ttFiber76Prefix24 = ttFiber76Prefix23 ++ [ttFiber76StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 24) []
    (chainClosureStep ttWord ttFiber76Prefix23 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 8) hparentBefore ttFiber76ReverseSingleStep24

theorem ttFiber76State24_in_pass1_full :
    ttFiber76StateAt 24 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix24 ++ [ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix24 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 24) ttFiber76State24_in_pass1_prefix24

theorem ttFiber76State25_in_pass1_prefix25 :
    ttFiber76StateAt 25 ∈ chainClosureStep ttWord ttFiber76Prefix25 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 9 ∈
      chainClosureStep ttWord ttFiber76Prefix24 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix24 = ttFiber76Prefix9 ++ [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24]
      (chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 9) ttFiber76State9_in_pass1_prefix9
  rw [show ttFiber76Prefix25 = ttFiber76Prefix24 ++ [ttFiber76StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 25) []
    (chainClosureStep ttWord ttFiber76Prefix24 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 9) hparentBefore ttFiber76ReverseSingleStep25

theorem ttFiber76State25_in_pass1_full :
    ttFiber76StateAt 25 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix25 ++ [ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix25 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 25) ttFiber76State25_in_pass1_prefix25

theorem ttFiber76State26_in_pass1_prefix26 :
    ttFiber76StateAt 26 ∈ chainClosureStep ttWord ttFiber76Prefix26 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 10 ∈
      chainClosureStep ttWord ttFiber76Prefix25 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix25 = ttFiber76Prefix10 ++ [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25]
      (chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 10) ttFiber76State10_in_pass1_prefix10
  rw [show ttFiber76Prefix26 = ttFiber76Prefix25 ++ [ttFiber76StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 26) []
    (chainClosureStep ttWord ttFiber76Prefix25 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 10) hparentBefore ttFiber76ReverseSingleStep26

theorem ttFiber76State26_in_pass1_full :
    ttFiber76StateAt 26 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix26 ++ [ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix26 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 26) ttFiber76State26_in_pass1_prefix26

theorem ttFiber76State27_in_pass1_prefix27 :
    ttFiber76StateAt 27 ∈ chainClosureStep ttWord ttFiber76Prefix27 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 11 ∈
      chainClosureStep ttWord ttFiber76Prefix26 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix26 = ttFiber76Prefix11 ++ [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26]
      (chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 11) ttFiber76State11_in_pass1_prefix11
  rw [show ttFiber76Prefix27 = ttFiber76Prefix26 ++ [ttFiber76StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 27) []
    (chainClosureStep ttWord ttFiber76Prefix26 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 11) hparentBefore ttFiber76ReverseSingleStep27

theorem ttFiber76State27_in_pass1_full :
    ttFiber76StateAt 27 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix27 ++ [ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix27 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 27) ttFiber76State27_in_pass1_prefix27

theorem ttFiber76State28_in_pass1_prefix28 :
    ttFiber76StateAt 28 ∈ chainClosureStep ttWord ttFiber76Prefix28 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 24 ∈
      chainClosureStep ttWord ttFiber76Prefix27 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix27 = ttFiber76Prefix24 ++ [ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27]
      (chainClosureStep ttWord ttFiber76Prefix24 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 24) ttFiber76State24_in_pass1_prefix24
  rw [show ttFiber76Prefix28 = ttFiber76Prefix27 ++ [ttFiber76StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 28) []
    (chainClosureStep ttWord ttFiber76Prefix27 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 24) hparentBefore ttFiber76ReverseSingleStep28

theorem ttFiber76State28_in_pass1_full :
    ttFiber76StateAt 28 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix28 ++ [ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix28 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 28) ttFiber76State28_in_pass1_prefix28

theorem ttFiber76State29_in_pass1_prefix29 :
    ttFiber76StateAt 29 ∈ chainClosureStep ttWord ttFiber76Prefix29 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 25 ∈
      chainClosureStep ttWord ttFiber76Prefix28 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix28 = ttFiber76Prefix25 ++ [ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28]
      (chainClosureStep ttWord ttFiber76Prefix25 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 25) ttFiber76State25_in_pass1_prefix25
  rw [show ttFiber76Prefix29 = ttFiber76Prefix28 ++ [ttFiber76StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 29) []
    (chainClosureStep ttWord ttFiber76Prefix28 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 25) hparentBefore ttFiber76ReverseSingleStep29

theorem ttFiber76State29_in_pass1_full :
    ttFiber76StateAt 29 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix29 ++ [ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix29 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 29) ttFiber76State29_in_pass1_prefix29

theorem ttFiber76State30_in_pass1_prefix30 :
    ttFiber76StateAt 30 ∈ chainClosureStep ttWord ttFiber76Prefix30 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 14 ∈
      chainClosureStep ttWord ttFiber76Prefix29 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix29 = ttFiber76Prefix14 ++ [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29]
      (chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 14) ttFiber76State14_in_pass1_prefix14
  rw [show ttFiber76Prefix30 = ttFiber76Prefix29 ++ [ttFiber76StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 30) []
    (chainClosureStep ttWord ttFiber76Prefix29 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 14) hparentBefore ttFiber76ReverseSingleStep30

theorem ttFiber76State30_in_pass1_full :
    ttFiber76StateAt 30 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix30 ++ [ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix30 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 30) ttFiber76State30_in_pass1_prefix30

theorem ttFiber76State31_in_pass1_prefix31 :
    ttFiber76StateAt 31 ∈ chainClosureStep ttWord ttFiber76Prefix31 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 15 ∈
      chainClosureStep ttWord ttFiber76Prefix30 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix30 = ttFiber76Prefix15 ++ [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30]
      (chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 15) ttFiber76State15_in_pass1_prefix15
  rw [show ttFiber76Prefix31 = ttFiber76Prefix30 ++ [ttFiber76StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 31) []
    (chainClosureStep ttWord ttFiber76Prefix30 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 15) hparentBefore ttFiber76ReverseSingleStep31

theorem ttFiber76State31_in_pass1_full :
    ttFiber76StateAt 31 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix31 ++ [ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix31 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 31) ttFiber76State31_in_pass1_prefix31

theorem ttFiber76State34_in_pass1_prefix34 :
    ttFiber76StateAt 34 ∈ chainClosureStep ttWord ttFiber76Prefix34 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 22 ∈
      chainClosureStep ttWord ttFiber76Prefix33 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix33 = ttFiber76Prefix22 ++ [ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33]
      (chainClosureStep ttWord ttFiber76Prefix22 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 22) ttFiber76State22_in_pass1_prefix22
  rw [show ttFiber76Prefix34 = ttFiber76Prefix33 ++ [ttFiber76StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 34) []
    (chainClosureStep ttWord ttFiber76Prefix33 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 22) hparentBefore ttFiber76ReverseSingleStep34

theorem ttFiber76State34_in_pass1_full :
    ttFiber76StateAt 34 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix34 ++ [ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix34 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 34) ttFiber76State34_in_pass1_prefix34

theorem ttFiber76State35_in_pass1_prefix35 :
    ttFiber76StateAt 35 ∈ chainClosureStep ttWord ttFiber76Prefix35 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 23 ∈
      chainClosureStep ttWord ttFiber76Prefix34 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix34 = ttFiber76Prefix23 ++ [ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34]
      (chainClosureStep ttWord ttFiber76Prefix23 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 23) ttFiber76State23_in_pass1_prefix23
  rw [show ttFiber76Prefix35 = ttFiber76Prefix34 ++ [ttFiber76StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 35) []
    (chainClosureStep ttWord ttFiber76Prefix34 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 23) hparentBefore ttFiber76ReverseSingleStep35

theorem ttFiber76State35_in_pass1_full :
    ttFiber76StateAt 35 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix35 ++ [ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix35 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 35) ttFiber76State35_in_pass1_prefix35

theorem ttFiber76State36_in_pass1_prefix36 :
    ttFiber76StateAt 36 ∈ chainClosureStep ttWord ttFiber76Prefix36 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 18 ∈
      chainClosureStep ttWord ttFiber76Prefix35 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix35 = ttFiber76Prefix18 ++ [ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35]
      (chainClosureStep ttWord ttFiber76Prefix18 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 18) ttFiber76State18_in_pass1_prefix18
  rw [show ttFiber76Prefix36 = ttFiber76Prefix35 ++ [ttFiber76StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 36) []
    (chainClosureStep ttWord ttFiber76Prefix35 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 18) hparentBefore ttFiber76ReverseSingleStep36

theorem ttFiber76State36_in_pass1_full :
    ttFiber76StateAt 36 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix36 ++ [ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix36 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 36) ttFiber76State36_in_pass1_prefix36

theorem ttFiber76State38_in_pass1_prefix38 :
    ttFiber76StateAt 38 ∈ chainClosureStep ttWord ttFiber76Prefix38 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 17 ∈
      chainClosureStep ttWord ttFiber76Prefix37 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix37 = ttFiber76Prefix17 ++ [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37]
      (chainClosureStep ttWord ttFiber76Prefix17 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 17) ttFiber76State17_in_pass1_prefix17
  rw [show ttFiber76Prefix38 = ttFiber76Prefix37 ++ [ttFiber76StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 38) []
    (chainClosureStep ttWord ttFiber76Prefix37 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 17) hparentBefore ttFiber76ReverseSingleStep38

theorem ttFiber76State38_in_pass1_full :
    ttFiber76StateAt 38 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix38 ++ [ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix38 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 38) ttFiber76State38_in_pass1_prefix38

theorem ttFiber76State39_in_pass1_prefix39 :
    ttFiber76StateAt 39 ∈ chainClosureStep ttWord ttFiber76Prefix39 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 16 ∈
      chainClosureStep ttWord ttFiber76Prefix38 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix38 = ttFiber76Prefix16 ++ [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38]
      (chainClosureStep ttWord ttFiber76Prefix16 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 16) ttFiber76State16_in_pass1_prefix16
  rw [show ttFiber76Prefix39 = ttFiber76Prefix38 ++ [ttFiber76StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 39) []
    (chainClosureStep ttWord ttFiber76Prefix38 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 16) hparentBefore ttFiber76ReverseSingleStep39

theorem ttFiber76State39_in_pass1_full :
    ttFiber76StateAt 39 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix39 ++ [ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix39 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 39) ttFiber76State39_in_pass1_prefix39

theorem ttFiber76State48_in_pass1_prefix48 :
    ttFiber76StateAt 48 ∈ chainClosureStep ttWord ttFiber76Prefix48 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 8 ∈
      chainClosureStep ttWord ttFiber76Prefix47 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix47 = ttFiber76Prefix8 ++ [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47]
      (chainClosureStep ttWord ttFiber76Prefix8 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 8) ttFiber76State8_in_pass1_prefix8
  rw [show ttFiber76Prefix48 = ttFiber76Prefix47 ++ [ttFiber76StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 48) []
    (chainClosureStep ttWord ttFiber76Prefix47 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 8) hparentBefore ttFiber76ReverseSingleStep48

theorem ttFiber76State48_in_pass1_full :
    ttFiber76StateAt 48 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix48 ++ [ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix48 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 48) ttFiber76State48_in_pass1_prefix48

theorem ttFiber76State49_in_pass1_prefix49 :
    ttFiber76StateAt 49 ∈ chainClosureStep ttWord ttFiber76Prefix49 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 9 ∈
      chainClosureStep ttWord ttFiber76Prefix48 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix48 = ttFiber76Prefix9 ++ [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48]
      (chainClosureStep ttWord ttFiber76Prefix9 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 9) ttFiber76State9_in_pass1_prefix9
  rw [show ttFiber76Prefix49 = ttFiber76Prefix48 ++ [ttFiber76StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 49) []
    (chainClosureStep ttWord ttFiber76Prefix48 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 9) hparentBefore ttFiber76ReverseSingleStep49

theorem ttFiber76State49_in_pass1_full :
    ttFiber76StateAt 49 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix49 ++ [ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix49 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 49) ttFiber76State49_in_pass1_prefix49

theorem ttFiber76State50_in_pass1_prefix50 :
    ttFiber76StateAt 50 ∈ chainClosureStep ttWord ttFiber76Prefix50 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 10 ∈
      chainClosureStep ttWord ttFiber76Prefix49 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix49 = ttFiber76Prefix10 ++ [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49]
      (chainClosureStep ttWord ttFiber76Prefix10 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 10) ttFiber76State10_in_pass1_prefix10
  rw [show ttFiber76Prefix50 = ttFiber76Prefix49 ++ [ttFiber76StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 50) []
    (chainClosureStep ttWord ttFiber76Prefix49 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 10) hparentBefore ttFiber76ReverseSingleStep50

theorem ttFiber76State50_in_pass1_full :
    ttFiber76StateAt 50 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix50 ++ [ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix50 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 50) ttFiber76State50_in_pass1_prefix50

theorem ttFiber76State51_in_pass1_prefix51 :
    ttFiber76StateAt 51 ∈ chainClosureStep ttWord ttFiber76Prefix51 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 11 ∈
      chainClosureStep ttWord ttFiber76Prefix50 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix50 = ttFiber76Prefix11 ++ [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50]
      (chainClosureStep ttWord ttFiber76Prefix11 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 11) ttFiber76State11_in_pass1_prefix11
  rw [show ttFiber76Prefix51 = ttFiber76Prefix50 ++ [ttFiber76StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 51) []
    (chainClosureStep ttWord ttFiber76Prefix50 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 11) hparentBefore ttFiber76ReverseSingleStep51

theorem ttFiber76State51_in_pass1_full :
    ttFiber76StateAt 51 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix51 ++ [ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix51 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 51) ttFiber76State51_in_pass1_prefix51

theorem ttFiber76State52_in_pass1_prefix52 :
    ttFiber76StateAt 52 ∈ chainClosureStep ttWord ttFiber76Prefix52 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 12 ∈
      chainClosureStep ttWord ttFiber76Prefix51 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix51 = ttFiber76Prefix12 ++ [ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51]
      (chainClosureStep ttWord ttFiber76Prefix12 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 12) ttFiber76State12_in_pass1_prefix12
  rw [show ttFiber76Prefix52 = ttFiber76Prefix51 ++ [ttFiber76StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 52) []
    (chainClosureStep ttWord ttFiber76Prefix51 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 12) hparentBefore ttFiber76ReverseSingleStep52

theorem ttFiber76State52_in_pass1_full :
    ttFiber76StateAt 52 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix52 ++ [ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix52 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 52) ttFiber76State52_in_pass1_prefix52

theorem ttFiber76State54_in_pass1_prefix54 :
    ttFiber76StateAt 54 ∈ chainClosureStep ttWord ttFiber76Prefix54 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 14 ∈
      chainClosureStep ttWord ttFiber76Prefix53 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix53 = ttFiber76Prefix14 ++ [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53]
      (chainClosureStep ttWord ttFiber76Prefix14 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 14) ttFiber76State14_in_pass1_prefix14
  rw [show ttFiber76Prefix54 = ttFiber76Prefix53 ++ [ttFiber76StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 54) []
    (chainClosureStep ttWord ttFiber76Prefix53 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 14) hparentBefore ttFiber76ReverseSingleStep54

theorem ttFiber76State54_in_pass1_full :
    ttFiber76StateAt 54 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix54 ++ [ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix54 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 54) ttFiber76State54_in_pass1_prefix54

theorem ttFiber76State55_in_pass1_prefix55 :
    ttFiber76StateAt 55 ∈ chainClosureStep ttWord ttFiber76Prefix55 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 15 ∈
      chainClosureStep ttWord ttFiber76Prefix54 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix54 = ttFiber76Prefix15 ++ [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54]
      (chainClosureStep ttWord ttFiber76Prefix15 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 15) ttFiber76State15_in_pass1_prefix15
  rw [show ttFiber76Prefix55 = ttFiber76Prefix54 ++ [ttFiber76StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 55) []
    (chainClosureStep ttWord ttFiber76Prefix54 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 15) hparentBefore ttFiber76ReverseSingleStep55

theorem ttFiber76State55_in_pass1_full :
    ttFiber76StateAt 55 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix55 ++ [ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix55 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 55) ttFiber76State55_in_pass1_prefix55

theorem ttFiber76State56_in_pass1_prefix56 :
    ttFiber76StateAt 56 ∈ chainClosureStep ttWord ttFiber76Prefix56 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 0 ∈
      chainClosureStep ttWord ttFiber76Prefix55 ([ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix55
      ([ttFiber76StateAt 0]) (ttFiber76StateAt 0) ttFiber76State0_in_pass0_full
  rw [show ttFiber76Prefix56 = ttFiber76Prefix55 ++ [ttFiber76StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 56) []
    (chainClosureStep ttWord ttFiber76Prefix55 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 0) hparentBefore ttFiber76ReverseSingleStep56

theorem ttFiber76State56_in_pass1_full :
    ttFiber76StateAt 56 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix56 ++ [ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix56 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 56) ttFiber76State56_in_pass1_prefix56

theorem ttFiber76State57_in_pass1_prefix57 :
    ttFiber76StateAt 57 ∈ chainClosureStep ttWord ttFiber76Prefix57 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 1 ∈
      chainClosureStep ttWord ttFiber76Prefix56 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix56 = ttFiber76Prefix1 ++ [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 2, ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56]
      (chainClosureStep ttWord ttFiber76Prefix1 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 1) ttFiber76State1_in_pass1_prefix1
  rw [show ttFiber76Prefix57 = ttFiber76Prefix56 ++ [ttFiber76StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 57) []
    (chainClosureStep ttWord ttFiber76Prefix56 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 1) hparentBefore ttFiber76ReverseSingleStep57

theorem ttFiber76State57_in_pass1_full :
    ttFiber76StateAt 57 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix57 ++ [ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix57 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 57) ttFiber76State57_in_pass1_prefix57

theorem ttFiber76State58_in_pass1_prefix58 :
    ttFiber76StateAt 58 ∈ chainClosureStep ttWord ttFiber76Prefix58 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 2 ∈
      chainClosureStep ttWord ttFiber76Prefix57 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix57 = ttFiber76Prefix2 ++ [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 3, ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57]
      (chainClosureStep ttWord ttFiber76Prefix2 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 2) ttFiber76State2_in_pass1_prefix2
  rw [show ttFiber76Prefix58 = ttFiber76Prefix57 ++ [ttFiber76StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 58) []
    (chainClosureStep ttWord ttFiber76Prefix57 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 2) hparentBefore ttFiber76ReverseSingleStep58

theorem ttFiber76State58_in_pass1_full :
    ttFiber76StateAt 58 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix58 ++ [ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix58 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 58) ttFiber76State58_in_pass1_prefix58

theorem ttFiber76State59_in_pass1_prefix59 :
    ttFiber76StateAt 59 ∈ chainClosureStep ttWord ttFiber76Prefix59 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 3 ∈
      chainClosureStep ttWord ttFiber76Prefix58 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix58 = ttFiber76Prefix3 ++ [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 4, ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58]
      (chainClosureStep ttWord ttFiber76Prefix3 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 3) ttFiber76State3_in_pass1_prefix3
  rw [show ttFiber76Prefix59 = ttFiber76Prefix58 ++ [ttFiber76StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 59) []
    (chainClosureStep ttWord ttFiber76Prefix58 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 3) hparentBefore ttFiber76ReverseSingleStep59

theorem ttFiber76State59_in_pass1_full :
    ttFiber76StateAt 59 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix59 ++ [ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix59 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 59) ttFiber76State59_in_pass1_prefix59

theorem ttFiber76State60_in_pass1_prefix60 :
    ttFiber76StateAt 60 ∈ chainClosureStep ttWord ttFiber76Prefix60 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 4 ∈
      chainClosureStep ttWord ttFiber76Prefix59 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix59 = ttFiber76Prefix4 ++ [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 5, ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59]
      (chainClosureStep ttWord ttFiber76Prefix4 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 4) ttFiber76State4_in_pass1_prefix4
  rw [show ttFiber76Prefix60 = ttFiber76Prefix59 ++ [ttFiber76StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 60) []
    (chainClosureStep ttWord ttFiber76Prefix59 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 4) hparentBefore ttFiber76ReverseSingleStep60

theorem ttFiber76State60_in_pass1_full :
    ttFiber76StateAt 60 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix60 ++ [ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix60 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 60) ttFiber76State60_in_pass1_prefix60

theorem ttFiber76State62_in_pass1_prefix62 :
    ttFiber76StateAt 62 ∈ chainClosureStep ttWord ttFiber76Prefix62 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 6 ∈
      chainClosureStep ttWord ttFiber76Prefix61 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix61 = ttFiber76Prefix6 ++ [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61]
      (chainClosureStep ttWord ttFiber76Prefix6 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 6) ttFiber76State6_in_pass1_prefix6
  rw [show ttFiber76Prefix62 = ttFiber76Prefix61 ++ [ttFiber76StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 62) []
    (chainClosureStep ttWord ttFiber76Prefix61 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 6) hparentBefore ttFiber76ReverseSingleStep62

theorem ttFiber76State62_in_pass1_full :
    ttFiber76StateAt 62 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix62 ++ [ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix62 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 62) ttFiber76State62_in_pass1_prefix62

theorem ttFiber76State63_in_pass1_prefix63 :
    ttFiber76StateAt 63 ∈ chainClosureStep ttWord ttFiber76Prefix63 ([ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 7 ∈
      chainClosureStep ttWord ttFiber76Prefix62 ([ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix62 = ttFiber76Prefix7 ++ [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62]
      (chainClosureStep ttWord ttFiber76Prefix7 ([ttFiber76StateAt 0]))
      (ttFiber76StateAt 7) ttFiber76State7_in_pass1_prefix7
  rw [show ttFiber76Prefix63 = ttFiber76Prefix62 ++ [ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 63) []
    (chainClosureStep ttWord ttFiber76Prefix62 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 7) hparentBefore ttFiber76ReverseSingleStep63

theorem ttFiber76State63_in_pass1_full :
    ttFiber76StateAt 63 ∈ chainClosureStep ttWord ttFiber76DirectStates ([ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber76Prefix63 ([ttFiber76StateAt 0]))
    (ttFiber76StateAt 63) ttFiber76State63_in_pass1_prefix63

theorem ttFiber76State5_in_pass2_prefix5 :
    ttFiber76StateAt 5 ∈ chainClosureStep ttWord ttFiber76Prefix5 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 7 ∈
      chainClosureStep ttWord ttFiber76Prefix4 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix4
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 7) ttFiber76State7_in_pass1_full
  rw [show ttFiber76Prefix5 = ttFiber76Prefix4 ++ [ttFiber76StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 5) []
    (chainClosureStep ttWord ttFiber76Prefix4 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 7) hparentBefore ttFiber76ReverseSingleStep5

theorem ttFiber76State5_in_pass2_full :
    ttFiber76StateAt 5 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix5 ++ [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix5 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 5) ttFiber76State5_in_pass2_prefix5

theorem ttFiber76State13_in_pass2_prefix13 :
    ttFiber76StateAt 13 ∈ chainClosureStep ttWord ttFiber76Prefix13 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 5 ∈
      chainClosureStep ttWord ttFiber76Prefix12 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix12 = ttFiber76Prefix5 ++ [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12]
      (chainClosureStep ttWord ttFiber76Prefix5 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 5) ttFiber76State5_in_pass2_prefix5
  rw [show ttFiber76Prefix13 = ttFiber76Prefix12 ++ [ttFiber76StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 13) []
    (chainClosureStep ttWord ttFiber76Prefix12 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 5) hparentBefore ttFiber76ReverseSingleStep13

theorem ttFiber76State13_in_pass2_full :
    ttFiber76StateAt 13 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix13 ++ [ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix13 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 13) ttFiber76State13_in_pass2_prefix13

theorem ttFiber76State32_in_pass2_prefix32 :
    ttFiber76StateAt 32 ∈ chainClosureStep ttWord ttFiber76Prefix32 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 48 ∈
      chainClosureStep ttWord ttFiber76Prefix31 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix31
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 48) ttFiber76State48_in_pass1_full
  rw [show ttFiber76Prefix32 = ttFiber76Prefix31 ++ [ttFiber76StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 32) []
    (chainClosureStep ttWord ttFiber76Prefix31 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 48) hparentBefore ttFiber76ReverseSingleStep32

theorem ttFiber76State32_in_pass2_full :
    ttFiber76StateAt 32 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix32 ++ [ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix32 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 32) ttFiber76State32_in_pass2_prefix32

theorem ttFiber76State33_in_pass2_prefix33 :
    ttFiber76StateAt 33 ∈ chainClosureStep ttWord ttFiber76Prefix33 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 49 ∈
      chainClosureStep ttWord ttFiber76Prefix32 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix32
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 49) ttFiber76State49_in_pass1_full
  rw [show ttFiber76Prefix33 = ttFiber76Prefix32 ++ [ttFiber76StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 33) []
    (chainClosureStep ttWord ttFiber76Prefix32 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 49) hparentBefore ttFiber76ReverseSingleStep33

theorem ttFiber76State33_in_pass2_full :
    ttFiber76StateAt 33 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix33 ++ [ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix33 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 33) ttFiber76State33_in_pass2_prefix33

theorem ttFiber76State37_in_pass2_prefix37 :
    ttFiber76StateAt 37 ∈ chainClosureStep ttWord ttFiber76Prefix37 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 39 ∈
      chainClosureStep ttWord ttFiber76Prefix36 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix36
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 39) ttFiber76State39_in_pass1_full
  rw [show ttFiber76Prefix37 = ttFiber76Prefix36 ++ [ttFiber76StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 37) []
    (chainClosureStep ttWord ttFiber76Prefix36 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 39) hparentBefore ttFiber76ReverseSingleStep37

theorem ttFiber76State37_in_pass2_full :
    ttFiber76StateAt 37 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix37 ++ [ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix37 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 37) ttFiber76State37_in_pass2_prefix37

theorem ttFiber76State40_in_pass2_prefix40 :
    ttFiber76StateAt 40 ∈ chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 56 ∈
      chainClosureStep ttWord ttFiber76Prefix39 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix39
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 56) ttFiber76State56_in_pass1_full
  rw [show ttFiber76Prefix40 = ttFiber76Prefix39 ++ [ttFiber76StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 40) []
    (chainClosureStep ttWord ttFiber76Prefix39 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 56) hparentBefore ttFiber76ReverseSingleStep40

theorem ttFiber76State40_in_pass2_full :
    ttFiber76StateAt 40 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix40 ++ [ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 40) ttFiber76State40_in_pass2_prefix40

theorem ttFiber76State41_in_pass2_prefix41 :
    ttFiber76StateAt 41 ∈ chainClosureStep ttWord ttFiber76Prefix41 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 57 ∈
      chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix40
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 57) ttFiber76State57_in_pass1_full
  rw [show ttFiber76Prefix41 = ttFiber76Prefix40 ++ [ttFiber76StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 41) []
    (chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 57) hparentBefore ttFiber76ReverseSingleStep41

theorem ttFiber76State41_in_pass2_full :
    ttFiber76StateAt 41 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix41 ++ [ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix41 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 41) ttFiber76State41_in_pass2_prefix41

theorem ttFiber76State42_in_pass2_prefix42 :
    ttFiber76StateAt 42 ∈ chainClosureStep ttWord ttFiber76Prefix42 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 58 ∈
      chainClosureStep ttWord ttFiber76Prefix41 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix41
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 58) ttFiber76State58_in_pass1_full
  rw [show ttFiber76Prefix42 = ttFiber76Prefix41 ++ [ttFiber76StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 42) []
    (chainClosureStep ttWord ttFiber76Prefix41 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 58) hparentBefore ttFiber76ReverseSingleStep42

theorem ttFiber76State42_in_pass2_full :
    ttFiber76StateAt 42 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix42 ++ [ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix42 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 42) ttFiber76State42_in_pass2_prefix42

theorem ttFiber76State43_in_pass2_prefix43 :
    ttFiber76StateAt 43 ∈ chainClosureStep ttWord ttFiber76Prefix43 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 40 ∈
      chainClosureStep ttWord ttFiber76Prefix42 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix42 = ttFiber76Prefix40 ++ [ttFiber76StateAt 41, ttFiber76StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 41, ttFiber76StateAt 42]
      (chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 40) ttFiber76State40_in_pass2_prefix40
  rw [show ttFiber76Prefix43 = ttFiber76Prefix42 ++ [ttFiber76StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 43) []
    (chainClosureStep ttWord ttFiber76Prefix42 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 40) hparentBefore ttFiber76ReverseSingleStep43

theorem ttFiber76State43_in_pass2_full :
    ttFiber76StateAt 43 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix43 ++ [ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix43 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 43) ttFiber76State43_in_pass2_prefix43

theorem ttFiber76State44_in_pass2_prefix44 :
    ttFiber76StateAt 44 ∈ chainClosureStep ttWord ttFiber76Prefix44 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 40 ∈
      chainClosureStep ttWord ttFiber76Prefix43 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix43 = ttFiber76Prefix40 ++ [ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43]
      (chainClosureStep ttWord ttFiber76Prefix40 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 40) ttFiber76State40_in_pass2_prefix40
  rw [show ttFiber76Prefix44 = ttFiber76Prefix43 ++ [ttFiber76StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 44) []
    (chainClosureStep ttWord ttFiber76Prefix43 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 40) hparentBefore ttFiber76ReverseSingleStep44

theorem ttFiber76State44_in_pass2_full :
    ttFiber76StateAt 44 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix44 ++ [ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix44 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 44) ttFiber76State44_in_pass2_prefix44

theorem ttFiber76State45_in_pass2_prefix45 :
    ttFiber76StateAt 45 ∈ chainClosureStep ttWord ttFiber76Prefix45 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 41 ∈
      chainClosureStep ttWord ttFiber76Prefix44 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix44 = ttFiber76Prefix41 ++ [ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44]
      (chainClosureStep ttWord ttFiber76Prefix41 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 41) ttFiber76State41_in_pass2_prefix41
  rw [show ttFiber76Prefix45 = ttFiber76Prefix44 ++ [ttFiber76StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 45) []
    (chainClosureStep ttWord ttFiber76Prefix44 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 41) hparentBefore ttFiber76ReverseSingleStep45

theorem ttFiber76State45_in_pass2_full :
    ttFiber76StateAt 45 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix45 ++ [ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix45 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 45) ttFiber76State45_in_pass2_prefix45

theorem ttFiber76State46_in_pass2_prefix46 :
    ttFiber76StateAt 46 ∈ chainClosureStep ttWord ttFiber76Prefix46 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 62 ∈
      chainClosureStep ttWord ttFiber76Prefix45 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix45
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 62) ttFiber76State62_in_pass1_full
  rw [show ttFiber76Prefix46 = ttFiber76Prefix45 ++ [ttFiber76StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 46) []
    (chainClosureStep ttWord ttFiber76Prefix45 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 62) hparentBefore ttFiber76ReverseSingleStep46

theorem ttFiber76State46_in_pass2_full :
    ttFiber76StateAt 46 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix46 ++ [ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix46 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 46) ttFiber76State46_in_pass2_prefix46

theorem ttFiber76State47_in_pass2_prefix47 :
    ttFiber76StateAt 47 ∈ chainClosureStep ttWord ttFiber76Prefix47 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 63 ∈
      chainClosureStep ttWord ttFiber76Prefix46 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber76Prefix46
      (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) (ttFiber76StateAt 63) ttFiber76State63_in_pass1_full
  rw [show ttFiber76Prefix47 = ttFiber76Prefix46 ++ [ttFiber76StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 47) []
    (chainClosureStep ttWord ttFiber76Prefix46 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 63) hparentBefore ttFiber76ReverseSingleStep47

theorem ttFiber76State47_in_pass2_full :
    ttFiber76StateAt 47 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix47 ++ [ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix47 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 47) ttFiber76State47_in_pass2_prefix47

theorem ttFiber76State53_in_pass2_prefix53 :
    ttFiber76StateAt 53 ∈ chainClosureStep ttWord ttFiber76Prefix53 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 13 ∈
      chainClosureStep ttWord ttFiber76Prefix52 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix52 = ttFiber76Prefix13 ++ [ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52]
      (chainClosureStep ttWord ttFiber76Prefix13 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 13) ttFiber76State13_in_pass2_prefix13
  rw [show ttFiber76Prefix53 = ttFiber76Prefix52 ++ [ttFiber76StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 53) []
    (chainClosureStep ttWord ttFiber76Prefix52 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 13) hparentBefore ttFiber76ReverseSingleStep53

theorem ttFiber76State53_in_pass2_full :
    ttFiber76StateAt 53 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix53 ++ [ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60, ttFiber76StateAt 61, ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix53 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 53) ttFiber76State53_in_pass2_prefix53

theorem ttFiber76State61_in_pass2_prefix61 :
    ttFiber76StateAt 61 ∈ chainClosureStep ttWord ttFiber76Prefix61 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  have hparentBefore : ttFiber76StateAt 5 ∈
      chainClosureStep ttWord ttFiber76Prefix60 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
    rw [show ttFiber76Prefix60 = ttFiber76Prefix5 ++ [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 6, ttFiber76StateAt 7, ttFiber76StateAt 8, ttFiber76StateAt 9, ttFiber76StateAt 10, ttFiber76StateAt 11, ttFiber76StateAt 12, ttFiber76StateAt 13, ttFiber76StateAt 14, ttFiber76StateAt 15, ttFiber76StateAt 16, ttFiber76StateAt 17, ttFiber76StateAt 18, ttFiber76StateAt 19, ttFiber76StateAt 20, ttFiber76StateAt 21, ttFiber76StateAt 22, ttFiber76StateAt 23, ttFiber76StateAt 24, ttFiber76StateAt 25, ttFiber76StateAt 26, ttFiber76StateAt 27, ttFiber76StateAt 28, ttFiber76StateAt 29, ttFiber76StateAt 30, ttFiber76StateAt 31, ttFiber76StateAt 32, ttFiber76StateAt 33, ttFiber76StateAt 34, ttFiber76StateAt 35, ttFiber76StateAt 36, ttFiber76StateAt 37, ttFiber76StateAt 38, ttFiber76StateAt 39, ttFiber76StateAt 40, ttFiber76StateAt 41, ttFiber76StateAt 42, ttFiber76StateAt 43, ttFiber76StateAt 44, ttFiber76StateAt 45, ttFiber76StateAt 46, ttFiber76StateAt 47, ttFiber76StateAt 48, ttFiber76StateAt 49, ttFiber76StateAt 50, ttFiber76StateAt 51, ttFiber76StateAt 52, ttFiber76StateAt 53, ttFiber76StateAt 54, ttFiber76StateAt 55, ttFiber76StateAt 56, ttFiber76StateAt 57, ttFiber76StateAt 58, ttFiber76StateAt 59, ttFiber76StateAt 60]
      (chainClosureStep ttWord ttFiber76Prefix5 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
      (ttFiber76StateAt 5) ttFiber76State5_in_pass2_prefix5
  rw [show ttFiber76Prefix61 = ttFiber76Prefix60 ++ [ttFiber76StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber76StateAt 61) []
    (chainClosureStep ttWord ttFiber76Prefix60 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 5) hparentBefore ttFiber76ReverseSingleStep61

theorem ttFiber76State61_in_pass2_full :
    ttFiber76StateAt 61 ∈ chainClosureStep ttWord ttFiber76DirectStates (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]) := by
  rw [show ttFiber76DirectStates = ttFiber76Prefix61 ++ [ttFiber76StateAt 62, ttFiber76StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber76StateAt 62, ttFiber76StateAt 63]
    (chainClosureStep ttWord ttFiber76Prefix61 (chainClosureStep ttWord ttFiber76DirectStates [ttFiber76StateAt 0]))
    (ttFiber76StateAt 61) ttFiber76State61_in_pass2_prefix61

theorem ttFiber76State0_in_close :
    ttFiber76StateAt 0 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber76DirectStates
    ttFiber76DirectStates.length [ttFiber76StateAt 0] (ttFiber76StateAt 0) (by simp)

theorem ttFiber76State1_in_close :
    ttFiber76StateAt 1 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 1 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 1) ttFiber76State1_in_pass1_full

theorem ttFiber76State2_in_close :
    ttFiber76StateAt 2 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 2 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 2) ttFiber76State2_in_pass1_full

theorem ttFiber76State3_in_close :
    ttFiber76StateAt 3 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 3 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 3) ttFiber76State3_in_pass1_full

theorem ttFiber76State4_in_close :
    ttFiber76StateAt 4 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 4 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 4) ttFiber76State4_in_pass1_full

theorem ttFiber76State5_in_close :
    ttFiber76StateAt 5 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 5 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 5) ttFiber76FirstPassGrows
    ttFiber76State5_in_pass2_full

theorem ttFiber76State6_in_close :
    ttFiber76StateAt 6 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 6 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 6) ttFiber76State6_in_pass1_full

theorem ttFiber76State7_in_close :
    ttFiber76StateAt 7 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 7 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 7) ttFiber76State7_in_pass1_full

theorem ttFiber76State8_in_close :
    ttFiber76StateAt 8 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 8 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 8) ttFiber76State8_in_pass1_full

theorem ttFiber76State9_in_close :
    ttFiber76StateAt 9 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 9 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 9) ttFiber76State9_in_pass1_full

theorem ttFiber76State10_in_close :
    ttFiber76StateAt 10 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 10 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 10) ttFiber76State10_in_pass1_full

theorem ttFiber76State11_in_close :
    ttFiber76StateAt 11 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 11 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 11) ttFiber76State11_in_pass1_full

theorem ttFiber76State12_in_close :
    ttFiber76StateAt 12 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 12 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 12) ttFiber76State12_in_pass1_full

theorem ttFiber76State13_in_close :
    ttFiber76StateAt 13 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 13 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 13) ttFiber76FirstPassGrows
    ttFiber76State13_in_pass2_full

theorem ttFiber76State14_in_close :
    ttFiber76StateAt 14 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 14 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 14) ttFiber76State14_in_pass1_full

theorem ttFiber76State15_in_close :
    ttFiber76StateAt 15 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 15 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 15) ttFiber76State15_in_pass1_full

theorem ttFiber76State16_in_close :
    ttFiber76StateAt 16 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 16 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 16) ttFiber76State16_in_pass1_full

theorem ttFiber76State17_in_close :
    ttFiber76StateAt 17 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 17 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 17) ttFiber76State17_in_pass1_full

theorem ttFiber76State18_in_close :
    ttFiber76StateAt 18 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 18 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 18) ttFiber76State18_in_pass1_full

theorem ttFiber76State19_in_close :
    ttFiber76StateAt 19 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 19 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 19) ttFiber76State19_in_pass1_full

theorem ttFiber76State20_in_close :
    ttFiber76StateAt 20 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 20 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 20) ttFiber76State20_in_pass1_full

theorem ttFiber76State21_in_close :
    ttFiber76StateAt 21 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 21 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 21) ttFiber76State21_in_pass1_full

theorem ttFiber76State22_in_close :
    ttFiber76StateAt 22 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 22 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 22) ttFiber76State22_in_pass1_full

theorem ttFiber76State23_in_close :
    ttFiber76StateAt 23 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 23 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 23) ttFiber76State23_in_pass1_full

theorem ttFiber76State24_in_close :
    ttFiber76StateAt 24 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 24 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 24) ttFiber76State24_in_pass1_full

theorem ttFiber76State25_in_close :
    ttFiber76StateAt 25 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 25 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 25) ttFiber76State25_in_pass1_full

theorem ttFiber76State26_in_close :
    ttFiber76StateAt 26 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 26 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 26) ttFiber76State26_in_pass1_full

theorem ttFiber76State27_in_close :
    ttFiber76StateAt 27 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 27 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 27) ttFiber76State27_in_pass1_full

theorem ttFiber76State28_in_close :
    ttFiber76StateAt 28 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 28 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 28) ttFiber76State28_in_pass1_full

theorem ttFiber76State29_in_close :
    ttFiber76StateAt 29 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 29 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 29) ttFiber76State29_in_pass1_full

theorem ttFiber76State30_in_close :
    ttFiber76StateAt 30 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 30 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 30) ttFiber76State30_in_pass1_full

theorem ttFiber76State31_in_close :
    ttFiber76StateAt 31 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 31 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 31) ttFiber76State31_in_pass1_full

theorem ttFiber76State32_in_close :
    ttFiber76StateAt 32 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 32 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 32) ttFiber76FirstPassGrows
    ttFiber76State32_in_pass2_full

theorem ttFiber76State33_in_close :
    ttFiber76StateAt 33 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 33 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 33) ttFiber76FirstPassGrows
    ttFiber76State33_in_pass2_full

theorem ttFiber76State34_in_close :
    ttFiber76StateAt 34 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 34 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 34) ttFiber76State34_in_pass1_full

theorem ttFiber76State35_in_close :
    ttFiber76StateAt 35 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 35 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 35) ttFiber76State35_in_pass1_full

theorem ttFiber76State36_in_close :
    ttFiber76StateAt 36 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 36 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 36) ttFiber76State36_in_pass1_full

theorem ttFiber76State37_in_close :
    ttFiber76StateAt 37 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 37 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 37) ttFiber76FirstPassGrows
    ttFiber76State37_in_pass2_full

theorem ttFiber76State38_in_close :
    ttFiber76StateAt 38 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 38 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 38) ttFiber76State38_in_pass1_full

theorem ttFiber76State39_in_close :
    ttFiber76StateAt 39 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 39 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 39) ttFiber76State39_in_pass1_full

theorem ttFiber76State40_in_close :
    ttFiber76StateAt 40 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 40 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 40) ttFiber76FirstPassGrows
    ttFiber76State40_in_pass2_full

theorem ttFiber76State41_in_close :
    ttFiber76StateAt 41 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 41 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 41) ttFiber76FirstPassGrows
    ttFiber76State41_in_pass2_full

theorem ttFiber76State42_in_close :
    ttFiber76StateAt 42 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 42 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 42) ttFiber76FirstPassGrows
    ttFiber76State42_in_pass2_full

theorem ttFiber76State43_in_close :
    ttFiber76StateAt 43 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 43 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 43) ttFiber76FirstPassGrows
    ttFiber76State43_in_pass2_full

theorem ttFiber76State44_in_close :
    ttFiber76StateAt 44 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 44 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 44) ttFiber76FirstPassGrows
    ttFiber76State44_in_pass2_full

theorem ttFiber76State45_in_close :
    ttFiber76StateAt 45 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 45 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 45) ttFiber76FirstPassGrows
    ttFiber76State45_in_pass2_full

theorem ttFiber76State46_in_close :
    ttFiber76StateAt 46 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 46 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 46) ttFiber76FirstPassGrows
    ttFiber76State46_in_pass2_full

theorem ttFiber76State47_in_close :
    ttFiber76StateAt 47 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 47 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 47) ttFiber76FirstPassGrows
    ttFiber76State47_in_pass2_full

theorem ttFiber76State48_in_close :
    ttFiber76StateAt 48 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 48 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 48) ttFiber76State48_in_pass1_full

theorem ttFiber76State49_in_close :
    ttFiber76StateAt 49 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 49 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 49) ttFiber76State49_in_pass1_full

theorem ttFiber76State50_in_close :
    ttFiber76StateAt 50 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 50 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 50) ttFiber76State50_in_pass1_full

theorem ttFiber76State51_in_close :
    ttFiber76StateAt 51 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 51 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 51) ttFiber76State51_in_pass1_full

theorem ttFiber76State52_in_close :
    ttFiber76StateAt 52 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 52 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 52) ttFiber76State52_in_pass1_full

theorem ttFiber76State53_in_close :
    ttFiber76StateAt 53 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 53 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 53) ttFiber76FirstPassGrows
    ttFiber76State53_in_pass2_full

theorem ttFiber76State54_in_close :
    ttFiber76StateAt 54 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 54 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 54) ttFiber76State54_in_pass1_full

theorem ttFiber76State55_in_close :
    ttFiber76StateAt 55 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 55 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 55) ttFiber76State55_in_pass1_full

theorem ttFiber76State56_in_close :
    ttFiber76StateAt 56 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 56 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 56) ttFiber76State56_in_pass1_full

theorem ttFiber76State57_in_close :
    ttFiber76StateAt 57 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 57 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 57) ttFiber76State57_in_pass1_full

theorem ttFiber76State58_in_close :
    ttFiber76StateAt 58 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 58 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 58) ttFiber76State58_in_pass1_full

theorem ttFiber76State59_in_close :
    ttFiber76StateAt 59 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 59 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 59) ttFiber76State59_in_pass1_full

theorem ttFiber76State60_in_close :
    ttFiber76StateAt 60 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 60 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 60) ttFiber76State60_in_pass1_full

theorem ttFiber76State61_in_close :
    ttFiber76StateAt 61 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 61 ∈ closeChainFiber ttWord ttFiber76DirectStates (62 + 2)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber76DirectStates 62
    [ttFiber76StateAt 0] (ttFiber76StateAt 61) ttFiber76FirstPassGrows
    ttFiber76State61_in_pass2_full

theorem ttFiber76State62_in_close :
    ttFiber76StateAt 62 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 62 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 62) ttFiber76State62_in_pass1_full

theorem ttFiber76State63_in_close :
    ttFiber76StateAt 63 ∈
      closeChainFiber ttWord ttFiber76DirectStates ttFiber76DirectStates.length
        [ttFiber76StateAt 0] := by
  change ttFiber76StateAt 63 ∈ closeChainFiber ttWord ttFiber76DirectStates (63 + 1)
    [ttFiber76StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber76DirectStates 63
    [ttFiber76StateAt 0] (ttFiber76StateAt 63) ttFiber76State63_in_pass1_full

theorem ttFiber76DirectConnected :
    chainFiberConnected ttWord ttFiber76DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber76DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber76State0_in_close
  · subst state
    exact ttFiber76State1_in_close
  · subst state
    exact ttFiber76State2_in_close
  · subst state
    exact ttFiber76State3_in_close
  · subst state
    exact ttFiber76State4_in_close
  · subst state
    exact ttFiber76State5_in_close
  · subst state
    exact ttFiber76State6_in_close
  · subst state
    exact ttFiber76State7_in_close
  · subst state
    exact ttFiber76State8_in_close
  · subst state
    exact ttFiber76State9_in_close
  · subst state
    exact ttFiber76State10_in_close
  · subst state
    exact ttFiber76State11_in_close
  · subst state
    exact ttFiber76State12_in_close
  · subst state
    exact ttFiber76State13_in_close
  · subst state
    exact ttFiber76State14_in_close
  · subst state
    exact ttFiber76State15_in_close
  · subst state
    exact ttFiber76State16_in_close
  · subst state
    exact ttFiber76State17_in_close
  · subst state
    exact ttFiber76State18_in_close
  · subst state
    exact ttFiber76State19_in_close
  · subst state
    exact ttFiber76State20_in_close
  · subst state
    exact ttFiber76State21_in_close
  · subst state
    exact ttFiber76State22_in_close
  · subst state
    exact ttFiber76State23_in_close
  · subst state
    exact ttFiber76State24_in_close
  · subst state
    exact ttFiber76State25_in_close
  · subst state
    exact ttFiber76State26_in_close
  · subst state
    exact ttFiber76State27_in_close
  · subst state
    exact ttFiber76State28_in_close
  · subst state
    exact ttFiber76State29_in_close
  · subst state
    exact ttFiber76State30_in_close
  · subst state
    exact ttFiber76State31_in_close
  · subst state
    exact ttFiber76State32_in_close
  · subst state
    exact ttFiber76State33_in_close
  · subst state
    exact ttFiber76State34_in_close
  · subst state
    exact ttFiber76State35_in_close
  · subst state
    exact ttFiber76State36_in_close
  · subst state
    exact ttFiber76State37_in_close
  · subst state
    exact ttFiber76State38_in_close
  · subst state
    exact ttFiber76State39_in_close
  · subst state
    exact ttFiber76State40_in_close
  · subst state
    exact ttFiber76State41_in_close
  · subst state
    exact ttFiber76State42_in_close
  · subst state
    exact ttFiber76State43_in_close
  · subst state
    exact ttFiber76State44_in_close
  · subst state
    exact ttFiber76State45_in_close
  · subst state
    exact ttFiber76State46_in_close
  · subst state
    exact ttFiber76State47_in_close
  · subst state
    exact ttFiber76State48_in_close
  · subst state
    exact ttFiber76State49_in_close
  · subst state
    exact ttFiber76State50_in_close
  · subst state
    exact ttFiber76State51_in_close
  · subst state
    exact ttFiber76State52_in_close
  · subst state
    exact ttFiber76State53_in_close
  · subst state
    exact ttFiber76State54_in_close
  · subst state
    exact ttFiber76State55_in_close
  · subst state
    exact ttFiber76State56_in_close
  · subst state
    exact ttFiber76State57_in_close
  · subst state
    exact ttFiber76State58_in_close
  · subst state
    exact ttFiber76State59_in_close
  · subst state
    exact ttFiber76State60_in_close
  · subst state
    exact ttFiber76State61_in_close
  · subst state
    exact ttFiber76State62_in_close
  · subst state
    exact ttFiber76State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
