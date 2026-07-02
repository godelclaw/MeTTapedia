import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype multi-pass direct closure bridge for generated length-two fiber ttFiber10

This module checks the proof shape for a generated `tau,tau` fiber whose
parent order requires two closure scans.  It remains a local bridge
prototype, not the final real `chainLKRInAudit` theorem.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber10StateAt (i : Nat) : List TauState :=
  directStates (ttFiber10RowAt i).sourceLeft (ttFiber10RowAt i).sourceRight

def ttFiber10DirectStates : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]

def ttFiber10Prefix0 : List (List TauState) :=
  [ttFiber10StateAt 0]

def ttFiber10Prefix1 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1]

def ttFiber10Prefix2 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2]

def ttFiber10Prefix3 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3]

def ttFiber10Prefix4 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4]

def ttFiber10Prefix5 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5]

def ttFiber10Prefix6 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6]

def ttFiber10Prefix7 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7]

def ttFiber10Prefix8 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8]

def ttFiber10Prefix9 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9]

def ttFiber10Prefix10 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10]

def ttFiber10Prefix11 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11]

def ttFiber10Prefix12 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12]

def ttFiber10Prefix13 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13]

def ttFiber10Prefix14 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14]

def ttFiber10Prefix15 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15]

def ttFiber10Prefix16 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16]

def ttFiber10Prefix17 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17]

def ttFiber10Prefix18 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18]

def ttFiber10Prefix19 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19]

def ttFiber10Prefix20 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20]

def ttFiber10Prefix21 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21]

def ttFiber10Prefix22 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22]

def ttFiber10Prefix23 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23]

def ttFiber10Prefix24 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24]

def ttFiber10Prefix25 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25]

def ttFiber10Prefix26 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26]

def ttFiber10Prefix27 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27]

def ttFiber10Prefix28 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28]

def ttFiber10Prefix29 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29]

def ttFiber10Prefix30 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30]

def ttFiber10Prefix31 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31]

def ttFiber10Prefix32 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32]

def ttFiber10Prefix33 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33]

def ttFiber10Prefix34 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34]

def ttFiber10Prefix35 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35]

def ttFiber10Prefix36 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36]

def ttFiber10Prefix37 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37]

def ttFiber10Prefix38 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38]

def ttFiber10Prefix39 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39]

def ttFiber10Prefix40 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40]

def ttFiber10Prefix41 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41]

def ttFiber10Prefix42 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42]

def ttFiber10Prefix43 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43]

def ttFiber10Prefix44 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44]

def ttFiber10Prefix45 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45]

def ttFiber10Prefix46 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46]

def ttFiber10Prefix47 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47]

def ttFiber10Prefix48 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48]

def ttFiber10Prefix49 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49]

def ttFiber10Prefix50 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50]

def ttFiber10Prefix51 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51]

def ttFiber10Prefix52 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52]

def ttFiber10Prefix53 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53]

def ttFiber10Prefix54 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54]

def ttFiber10Prefix55 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55]

def ttFiber10Prefix56 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56]

def ttFiber10Prefix57 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57]

def ttFiber10Prefix58 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58]

def ttFiber10Prefix59 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59]

def ttFiber10Prefix60 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60]

def ttFiber10Prefix61 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61]

def ttFiber10Prefix62 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62]

def ttFiber10Prefix63 : List (List TauState) :=
  [ttFiber10StateAt 0, ttFiber10StateAt 1, ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]

theorem ttFiber10ReverseRow_1_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk0] at h
  exact h.2

theorem ttFiber10ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 1)
      (ttFiber10RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 1) (by decide) ttFiber10ReverseRow_1_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_2_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk1] at h
  exact h.1

theorem ttFiber10ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 2)
      (ttFiber10RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 2) (by decide) ttFiber10ReverseRow_2_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_3_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk1] at h
  exact h.2

theorem ttFiber10ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 3)
      (ttFiber10RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 3) (by decide) ttFiber10ReverseRow_3_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_4_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk2] at h
  exact h.1

theorem ttFiber10ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 4)
      (ttFiber10RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 4) (by decide) ttFiber10ReverseRow_4_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_5_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk2] at h
  exact h.2

theorem ttFiber10ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 5)
      (ttFiber10RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 5) (by decide) ttFiber10ReverseRow_5_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_6_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk3] at h
  exact h.1

theorem ttFiber10ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 6)
      (ttFiber10RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 6) (by decide) ttFiber10ReverseRow_6_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_7_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk3] at h
  exact h.2

theorem ttFiber10ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 7)
      (ttFiber10RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 7) (by decide) ttFiber10ReverseRow_7_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_8_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk4] at h
  exact h.1

theorem ttFiber10ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 8)
      (ttFiber10RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 8) (by decide) ttFiber10ReverseRow_8_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_9_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk4] at h
  exact h.2

theorem ttFiber10ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 9)
      (ttFiber10RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 9) (by decide) ttFiber10ReverseRow_9_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_10_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk5] at h
  exact h.1

theorem ttFiber10ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 10)
      (ttFiber10RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 10) (by decide) ttFiber10ReverseRow_10_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_11_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk5] at h
  exact h.2

theorem ttFiber10ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 11)
      (ttFiber10RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 11) (by decide) ttFiber10ReverseRow_11_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_12_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk6] at h
  exact h.1

theorem ttFiber10ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 4) (ttFiber10StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 4) (ttFiber10StateAt 12)
      (ttFiber10RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 12) (by decide) ttFiber10ReverseRow_12_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_13_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk6] at h
  exact h.2

theorem ttFiber10ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 5) (ttFiber10StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 5) (ttFiber10StateAt 13)
      (ttFiber10RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 13) (by decide) ttFiber10ReverseRow_13_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_14_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk7] at h
  exact h.1

theorem ttFiber10ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 14)
      (ttFiber10RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 14) (by decide) ttFiber10ReverseRow_14_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_15_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk7] at h
  exact h.2

theorem ttFiber10ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 15)
      (ttFiber10RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 15) (by decide) ttFiber10ReverseRow_15_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_16_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk8] at h
  exact h.1

theorem ttFiber10ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 16)
      (ttFiber10RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 16) (by decide) ttFiber10ReverseRow_16_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_17_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk8] at h
  exact h.2

theorem ttFiber10ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 17)
      (ttFiber10RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 17) (by decide) ttFiber10ReverseRow_17_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_18_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk9] at h
  exact h.1

theorem ttFiber10ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 18)
      (ttFiber10RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 18) (by decide) ttFiber10ReverseRow_18_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_19_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk9] at h
  exact h.2

theorem ttFiber10ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 19)
      (ttFiber10RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 19) (by decide) ttFiber10ReverseRow_19_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_20_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk10] at h
  exact h.1

theorem ttFiber10ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 16) (ttFiber10StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 16) (ttFiber10StateAt 20)
      (ttFiber10RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 20) (by decide) ttFiber10ReverseRow_20_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_21_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk10] at h
  exact h.2

theorem ttFiber10ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 17) (ttFiber10StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 17) (ttFiber10StateAt 21)
      (ttFiber10RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 21) (by decide) ttFiber10ReverseRow_21_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_22_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk11] at h
  exact h.1

theorem ttFiber10ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 22)
      (ttFiber10RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 22) (by decide) ttFiber10ReverseRow_22_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_23_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk11] at h
  exact h.2

theorem ttFiber10ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 23)
      (ttFiber10RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 23) (by decide) ttFiber10ReverseRow_23_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_24_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk12] at h
  exact h.1

theorem ttFiber10ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 8) (ttFiber10StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 8) (ttFiber10StateAt 24)
      (ttFiber10RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 24) (by decide) ttFiber10ReverseRow_24_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_25_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk12] at h
  exact h.2

theorem ttFiber10ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 9) (ttFiber10StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 9) (ttFiber10StateAt 25)
      (ttFiber10RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 25) (by decide) ttFiber10ReverseRow_25_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_26_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk13] at h
  exact h.1

theorem ttFiber10ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 10) (ttFiber10StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 10) (ttFiber10StateAt 26)
      (ttFiber10RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 26) (by decide) ttFiber10ReverseRow_26_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_27_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk13] at h
  exact h.2

theorem ttFiber10ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 11) (ttFiber10StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 11) (ttFiber10StateAt 27)
      (ttFiber10RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 27) (by decide) ttFiber10ReverseRow_27_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_28_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk14] at h
  exact h.1

theorem ttFiber10ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 24) (ttFiber10StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 24) (ttFiber10StateAt 28)
      (ttFiber10RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 28) (by decide) ttFiber10ReverseRow_28_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_29_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk14] at h
  exact h.2

theorem ttFiber10ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 25) (ttFiber10StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 25) (ttFiber10StateAt 29)
      (ttFiber10RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 29) (by decide) ttFiber10ReverseRow_29_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_30_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk15] at h
  exact h.1

theorem ttFiber10ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 14) (ttFiber10StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 14) (ttFiber10StateAt 30)
      (ttFiber10RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 30) (by decide) ttFiber10ReverseRow_30_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_31_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk15] at h
  exact h.2

theorem ttFiber10ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 15) (ttFiber10StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 15) (ttFiber10StateAt 31)
      (ttFiber10RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 31) (by decide) ttFiber10ReverseRow_31_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_32_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk16] at h
  exact h.1

theorem ttFiber10ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 48) (ttFiber10StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 48) (ttFiber10StateAt 32)
      (ttFiber10RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 32) (by decide) ttFiber10ReverseRow_32_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_33_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk16] at h
  exact h.2

theorem ttFiber10ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 49) (ttFiber10StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 49) (ttFiber10StateAt 33)
      (ttFiber10RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 33) (by decide) ttFiber10ReverseRow_33_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_34_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk17] at h
  exact h.1

theorem ttFiber10ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 22) (ttFiber10StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 22) (ttFiber10StateAt 34)
      (ttFiber10RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 34) (by decide) ttFiber10ReverseRow_34_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_35_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk17] at h
  exact h.2

theorem ttFiber10ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 23) (ttFiber10StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 23) (ttFiber10StateAt 35)
      (ttFiber10RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 35) (by decide) ttFiber10ReverseRow_35_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_36_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk18] at h
  exact h.1

theorem ttFiber10ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 18) (ttFiber10StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 18) (ttFiber10StateAt 36)
      (ttFiber10RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 36) (by decide) ttFiber10ReverseRow_36_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_37_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk18] at h
  exact h.2

theorem ttFiber10ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 39) (ttFiber10StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 39) (ttFiber10StateAt 37)
      (ttFiber10RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 37) (by decide) ttFiber10ReverseRow_37_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_38_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk19] at h
  exact h.1

theorem ttFiber10ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 17) (ttFiber10StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 17) (ttFiber10StateAt 38)
      (ttFiber10RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 38) (by decide) ttFiber10ReverseRow_38_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_39_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk19] at h
  exact h.2

theorem ttFiber10ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 16) (ttFiber10StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 16) (ttFiber10StateAt 39)
      (ttFiber10RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 39) (by decide) ttFiber10ReverseRow_39_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_40_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk20] at h
  exact h.1

theorem ttFiber10ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 56) (ttFiber10StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 56) (ttFiber10StateAt 40)
      (ttFiber10RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 40) (by decide) ttFiber10ReverseRow_40_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_41_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk20] at h
  exact h.2

theorem ttFiber10ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 57) (ttFiber10StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 57) (ttFiber10StateAt 41)
      (ttFiber10RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 41) (by decide) ttFiber10ReverseRow_41_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_42_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk21] at h
  exact h.1

theorem ttFiber10ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 58) (ttFiber10StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 58) (ttFiber10StateAt 42)
      (ttFiber10RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 42) (by decide) ttFiber10ReverseRow_42_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_43_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk21] at h
  exact h.2

theorem ttFiber10ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 40) (ttFiber10StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 40) (ttFiber10StateAt 43)
      (ttFiber10RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 43) (by decide) ttFiber10ReverseRow_43_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_44_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk22] at h
  exact h.1

theorem ttFiber10ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 40) (ttFiber10StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 40) (ttFiber10StateAt 44)
      (ttFiber10RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 44) (by decide) ttFiber10ReverseRow_44_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_45_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk22] at h
  exact h.2

theorem ttFiber10ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 41) (ttFiber10StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 41) (ttFiber10StateAt 45)
      (ttFiber10RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 45) (by decide) ttFiber10ReverseRow_45_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_46_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk23] at h
  exact h.1

theorem ttFiber10ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 62) (ttFiber10StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 62) (ttFiber10StateAt 46)
      (ttFiber10RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 46) (by decide) ttFiber10ReverseRow_46_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_47_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk23] at h
  exact h.2

theorem ttFiber10ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 63) (ttFiber10StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 63) (ttFiber10StateAt 47)
      (ttFiber10RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 47) (by decide) ttFiber10ReverseRow_47_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_48_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk24] at h
  exact h.1

theorem ttFiber10ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 8) (ttFiber10StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 8) (ttFiber10StateAt 48)
      (ttFiber10RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 48) (by decide) ttFiber10ReverseRow_48_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_49_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk24] at h
  exact h.2

theorem ttFiber10ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 9) (ttFiber10StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 9) (ttFiber10StateAt 49)
      (ttFiber10RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 49) (by decide) ttFiber10ReverseRow_49_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_50_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk25] at h
  exact h.1

theorem ttFiber10ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 10) (ttFiber10StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 10) (ttFiber10StateAt 50)
      (ttFiber10RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 50) (by decide) ttFiber10ReverseRow_50_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_51_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk25] at h
  exact h.2

theorem ttFiber10ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 11) (ttFiber10StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 11) (ttFiber10StateAt 51)
      (ttFiber10RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 51) (by decide) ttFiber10ReverseRow_51_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_52_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk26] at h
  exact h.1

theorem ttFiber10ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 12) (ttFiber10StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 12) (ttFiber10StateAt 52)
      (ttFiber10RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 52) (by decide) ttFiber10ReverseRow_52_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_53_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk26] at h
  exact h.2

theorem ttFiber10ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 13) (ttFiber10StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 13) (ttFiber10StateAt 53)
      (ttFiber10RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 53) (by decide) ttFiber10ReverseRow_53_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_54_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk27] at h
  exact h.1

theorem ttFiber10ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 14) (ttFiber10StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 14) (ttFiber10StateAt 54)
      (ttFiber10RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 54) (by decide) ttFiber10ReverseRow_54_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_55_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk27] at h
  exact h.2

theorem ttFiber10ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 15) (ttFiber10StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 15) (ttFiber10StateAt 55)
      (ttFiber10RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 55) (by decide) ttFiber10ReverseRow_55_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_56_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk28] at h
  exact h.1

theorem ttFiber10ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 0) (ttFiber10StateAt 56)
      (ttFiber10RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 56) (by decide) ttFiber10ReverseRow_56_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_57_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk28] at h
  exact h.2

theorem ttFiber10ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 1) (ttFiber10StateAt 57)
      (ttFiber10RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 57) (by decide) ttFiber10ReverseRow_57_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_58_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk29] at h
  exact h.1

theorem ttFiber10ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 2) (ttFiber10StateAt 58)
      (ttFiber10RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 58) (by decide) ttFiber10ReverseRow_58_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_59_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk29] at h
  exact h.2

theorem ttFiber10ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 3) (ttFiber10StateAt 59)
      (ttFiber10RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 59) (by decide) ttFiber10ReverseRow_59_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_60_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk30] at h
  exact h.1

theorem ttFiber10ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 4) (ttFiber10StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 4) (ttFiber10StateAt 60)
      (ttFiber10RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 60) (by decide) ttFiber10ReverseRow_60_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_61_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk30] at h
  exact h.2

theorem ttFiber10ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 5) (ttFiber10StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 5) (ttFiber10StateAt 61)
      (ttFiber10RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 61) (by decide) ttFiber10ReverseRow_61_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_62_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk31] at h
  exact h.1

theorem ttFiber10ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 6) (ttFiber10StateAt 62)
      (ttFiber10RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 62) (by decide) ttFiber10ReverseRow_62_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10ReverseRow_63_ok' :
    directRowReverseValid ttFiber10Key ttFiber10Expected (ttFiber10RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber10Chunk31] at h
  exact h.2

theorem ttFiber10ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber10StateAt 7) (ttFiber10StateAt 63)
      (ttFiber10RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber10Key ttFiber10Expected
      (ttFiber10RowAt 63) (by decide) ttFiber10ReverseRow_63_ok'
    simpa [ttFiber10StateAt, ttFiber10RowAt, ttFiber10Rows, listGetD, directRow] using h

theorem ttFiber10FirstPassGrows :
    ((chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]).length ==
      [ttFiber10StateAt 0].length) = false := by
  have hroot : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber10DirectStates [ttFiber10StateAt 0]
      (ttFiber10StateAt 0) (by simp)
  have hnew : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber10DirectStates [ttFiber10StateAt 0]
      (ttFiber10StateAt 0) (ttFiber10StateAt 1) (by decide) (by simp)
      ttFiber10ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0])
    (ttFiber10StateAt 0) (ttFiber10StateAt 1) hroot hnew (by decide)

theorem ttFiber10State0_in_pass0_full :
    ttFiber10StateAt 0 ∈ [ttFiber10StateAt 0] := by
  simp

theorem ttFiber10State1_in_pass1_prefix1 :
    ttFiber10StateAt 1 ∈ chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix0 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix0
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix1 = ttFiber10Prefix0 ++ [ttFiber10StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 1) []
    (chainClosureStep ttWord ttFiber10Prefix0 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep1

theorem ttFiber10State1_in_pass1_full :
    ttFiber10StateAt 1 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix1 ++ [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1

theorem ttFiber10State2_in_pass1_prefix2 :
    ttFiber10StateAt 2 ∈ chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix1
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix2 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 2) []
    (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep2

theorem ttFiber10State2_in_pass1_full :
    ttFiber10StateAt 2 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix2 ++ [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 2) ttFiber10State2_in_pass1_prefix2

theorem ttFiber10State3_in_pass1_prefix3 :
    ttFiber10StateAt 3 ∈ chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix2 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2]
      (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1
  rw [show ttFiber10Prefix3 = ttFiber10Prefix2 ++ [ttFiber10StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 3) []
    (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) hparentBefore ttFiber10ReverseSingleStep3

theorem ttFiber10State3_in_pass1_full :
    ttFiber10StateAt 3 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix3 ++ [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 3) ttFiber10State3_in_pass1_prefix3

theorem ttFiber10State4_in_pass1_prefix4 :
    ttFiber10StateAt 4 ∈ chainClosureStep ttWord ttFiber10Prefix4 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 2 ∈
      chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix3 = ttFiber10Prefix2 ++ [ttFiber10StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 3]
      (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 2) ttFiber10State2_in_pass1_prefix2
  rw [show ttFiber10Prefix4 = ttFiber10Prefix3 ++ [ttFiber10StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 4) []
    (chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 2) hparentBefore ttFiber10ReverseSingleStep4

theorem ttFiber10State4_in_pass1_full :
    ttFiber10StateAt 4 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix4 ++ [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix4 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 4) ttFiber10State4_in_pass1_prefix4

theorem ttFiber10State6_in_pass1_prefix6 :
    ttFiber10StateAt 6 ∈ chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10Prefix5 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix5 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5]
      (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1
  rw [show ttFiber10Prefix6 = ttFiber10Prefix5 ++ [ttFiber10StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 6) []
    (chainClosureStep ttWord ttFiber10Prefix5 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) hparentBefore ttFiber10ReverseSingleStep6

theorem ttFiber10State6_in_pass1_full :
    ttFiber10StateAt 6 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix6 ++ [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 6) ttFiber10State6_in_pass1_prefix6

theorem ttFiber10State7_in_pass1_prefix7 :
    ttFiber10StateAt 7 ∈ chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix6
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix7 = ttFiber10Prefix6 ++ [ttFiber10StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 7) []
    (chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep7

theorem ttFiber10State7_in_pass1_full :
    ttFiber10StateAt 7 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix7 ++ [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 7) ttFiber10State7_in_pass1_prefix7

theorem ttFiber10State8_in_pass1_prefix8 :
    ttFiber10StateAt 8 ∈ chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix7
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix8 = ttFiber10Prefix7 ++ [ttFiber10StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 8) []
    (chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep8

theorem ttFiber10State8_in_pass1_full :
    ttFiber10StateAt 8 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix8 ++ [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 8) ttFiber10State8_in_pass1_prefix8

theorem ttFiber10State9_in_pass1_prefix9 :
    ttFiber10StateAt 9 ∈ chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix8 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8]
      (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1
  rw [show ttFiber10Prefix9 = ttFiber10Prefix8 ++ [ttFiber10StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 9) []
    (chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) hparentBefore ttFiber10ReverseSingleStep9

theorem ttFiber10State9_in_pass1_full :
    ttFiber10StateAt 9 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix9 ++ [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 9) ttFiber10State9_in_pass1_prefix9

theorem ttFiber10State10_in_pass1_prefix10 :
    ttFiber10StateAt 10 ∈ chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 2 ∈
      chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix9 = ttFiber10Prefix2 ++ [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9]
      (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 2) ttFiber10State2_in_pass1_prefix2
  rw [show ttFiber10Prefix10 = ttFiber10Prefix9 ++ [ttFiber10StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 10) []
    (chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 2) hparentBefore ttFiber10ReverseSingleStep10

theorem ttFiber10State10_in_pass1_full :
    ttFiber10StateAt 10 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix10 ++ [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 10) ttFiber10State10_in_pass1_prefix10

theorem ttFiber10State11_in_pass1_prefix11 :
    ttFiber10StateAt 11 ∈ chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 3 ∈
      chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix10 = ttFiber10Prefix3 ++ [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10]
      (chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 3) ttFiber10State3_in_pass1_prefix3
  rw [show ttFiber10Prefix11 = ttFiber10Prefix10 ++ [ttFiber10StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 11) []
    (chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 3) hparentBefore ttFiber10ReverseSingleStep11

theorem ttFiber10State11_in_pass1_full :
    ttFiber10StateAt 11 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix11 ++ [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 11) ttFiber10State11_in_pass1_prefix11

theorem ttFiber10State12_in_pass1_prefix12 :
    ttFiber10StateAt 12 ∈ chainClosureStep ttWord ttFiber10Prefix12 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 4 ∈
      chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix11 = ttFiber10Prefix4 ++ [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11]
      (chainClosureStep ttWord ttFiber10Prefix4 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 4) ttFiber10State4_in_pass1_prefix4
  rw [show ttFiber10Prefix12 = ttFiber10Prefix11 ++ [ttFiber10StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 12) []
    (chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 4) hparentBefore ttFiber10ReverseSingleStep12

theorem ttFiber10State12_in_pass1_full :
    ttFiber10StateAt 12 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix12 ++ [ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix12 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 12) ttFiber10State12_in_pass1_prefix12

theorem ttFiber10State14_in_pass1_prefix14 :
    ttFiber10StateAt 14 ∈ chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 6 ∈
      chainClosureStep ttWord ttFiber10Prefix13 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix13 = ttFiber10Prefix6 ++ [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13]
      (chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 6) ttFiber10State6_in_pass1_prefix6
  rw [show ttFiber10Prefix14 = ttFiber10Prefix13 ++ [ttFiber10StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 14) []
    (chainClosureStep ttWord ttFiber10Prefix13 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 6) hparentBefore ttFiber10ReverseSingleStep14

theorem ttFiber10State14_in_pass1_full :
    ttFiber10StateAt 14 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix14 ++ [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 14) ttFiber10State14_in_pass1_prefix14

theorem ttFiber10State15_in_pass1_prefix15 :
    ttFiber10StateAt 15 ∈ chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 7 ∈
      chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix14 = ttFiber10Prefix7 ++ [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14]
      (chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 7) ttFiber10State7_in_pass1_prefix7
  rw [show ttFiber10Prefix15 = ttFiber10Prefix14 ++ [ttFiber10StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 15) []
    (chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 7) hparentBefore ttFiber10ReverseSingleStep15

theorem ttFiber10State15_in_pass1_full :
    ttFiber10StateAt 15 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix15 ++ [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 15) ttFiber10State15_in_pass1_prefix15

theorem ttFiber10State16_in_pass1_prefix16 :
    ttFiber10StateAt 16 ∈ chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix15
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix16 = ttFiber10Prefix15 ++ [ttFiber10StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 16) []
    (chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep16

theorem ttFiber10State16_in_pass1_full :
    ttFiber10StateAt 16 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix16 ++ [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 16) ttFiber10State16_in_pass1_prefix16

theorem ttFiber10State17_in_pass1_prefix17 :
    ttFiber10StateAt 17 ∈ chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix16 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16]
      (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1
  rw [show ttFiber10Prefix17 = ttFiber10Prefix16 ++ [ttFiber10StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 17) []
    (chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) hparentBefore ttFiber10ReverseSingleStep17

theorem ttFiber10State17_in_pass1_full :
    ttFiber10StateAt 17 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix17 ++ [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 17) ttFiber10State17_in_pass1_prefix17

theorem ttFiber10State18_in_pass1_prefix18 :
    ttFiber10StateAt 18 ∈ chainClosureStep ttWord ttFiber10Prefix18 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 2 ∈
      chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix17 = ttFiber10Prefix2 ++ [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17]
      (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 2) ttFiber10State2_in_pass1_prefix2
  rw [show ttFiber10Prefix18 = ttFiber10Prefix17 ++ [ttFiber10StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 18) []
    (chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 2) hparentBefore ttFiber10ReverseSingleStep18

theorem ttFiber10State18_in_pass1_full :
    ttFiber10StateAt 18 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix18 ++ [ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix18 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 18) ttFiber10State18_in_pass1_prefix18

theorem ttFiber10State19_in_pass1_prefix19 :
    ttFiber10StateAt 19 ∈ chainClosureStep ttWord ttFiber10Prefix19 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 3 ∈
      chainClosureStep ttWord ttFiber10Prefix18 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix18 = ttFiber10Prefix3 ++ [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18]
      (chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 3) ttFiber10State3_in_pass1_prefix3
  rw [show ttFiber10Prefix19 = ttFiber10Prefix18 ++ [ttFiber10StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 19) []
    (chainClosureStep ttWord ttFiber10Prefix18 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 3) hparentBefore ttFiber10ReverseSingleStep19

theorem ttFiber10State19_in_pass1_full :
    ttFiber10StateAt 19 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix19 ++ [ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix19 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 19) ttFiber10State19_in_pass1_prefix19

theorem ttFiber10State20_in_pass1_prefix20 :
    ttFiber10StateAt 20 ∈ chainClosureStep ttWord ttFiber10Prefix20 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 16 ∈
      chainClosureStep ttWord ttFiber10Prefix19 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix19 = ttFiber10Prefix16 ++ [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19]
      (chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 16) ttFiber10State16_in_pass1_prefix16
  rw [show ttFiber10Prefix20 = ttFiber10Prefix19 ++ [ttFiber10StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 20) []
    (chainClosureStep ttWord ttFiber10Prefix19 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 16) hparentBefore ttFiber10ReverseSingleStep20

theorem ttFiber10State20_in_pass1_full :
    ttFiber10StateAt 20 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix20 ++ [ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix20 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 20) ttFiber10State20_in_pass1_prefix20

theorem ttFiber10State21_in_pass1_prefix21 :
    ttFiber10StateAt 21 ∈ chainClosureStep ttWord ttFiber10Prefix21 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 17 ∈
      chainClosureStep ttWord ttFiber10Prefix20 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix20 = ttFiber10Prefix17 ++ [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20]
      (chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 17) ttFiber10State17_in_pass1_prefix17
  rw [show ttFiber10Prefix21 = ttFiber10Prefix20 ++ [ttFiber10StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 21) []
    (chainClosureStep ttWord ttFiber10Prefix20 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 17) hparentBefore ttFiber10ReverseSingleStep21

theorem ttFiber10State21_in_pass1_full :
    ttFiber10StateAt 21 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix21 ++ [ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix21 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 21) ttFiber10State21_in_pass1_prefix21

theorem ttFiber10State22_in_pass1_prefix22 :
    ttFiber10StateAt 22 ∈ chainClosureStep ttWord ttFiber10Prefix22 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 6 ∈
      chainClosureStep ttWord ttFiber10Prefix21 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix21 = ttFiber10Prefix6 ++ [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21]
      (chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 6) ttFiber10State6_in_pass1_prefix6
  rw [show ttFiber10Prefix22 = ttFiber10Prefix21 ++ [ttFiber10StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 22) []
    (chainClosureStep ttWord ttFiber10Prefix21 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 6) hparentBefore ttFiber10ReverseSingleStep22

theorem ttFiber10State22_in_pass1_full :
    ttFiber10StateAt 22 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix22 ++ [ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix22 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 22) ttFiber10State22_in_pass1_prefix22

theorem ttFiber10State23_in_pass1_prefix23 :
    ttFiber10StateAt 23 ∈ chainClosureStep ttWord ttFiber10Prefix23 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 7 ∈
      chainClosureStep ttWord ttFiber10Prefix22 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix22 = ttFiber10Prefix7 ++ [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22]
      (chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 7) ttFiber10State7_in_pass1_prefix7
  rw [show ttFiber10Prefix23 = ttFiber10Prefix22 ++ [ttFiber10StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 23) []
    (chainClosureStep ttWord ttFiber10Prefix22 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 7) hparentBefore ttFiber10ReverseSingleStep23

theorem ttFiber10State23_in_pass1_full :
    ttFiber10StateAt 23 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix23 ++ [ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix23 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 23) ttFiber10State23_in_pass1_prefix23

theorem ttFiber10State24_in_pass1_prefix24 :
    ttFiber10StateAt 24 ∈ chainClosureStep ttWord ttFiber10Prefix24 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 8 ∈
      chainClosureStep ttWord ttFiber10Prefix23 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix23 = ttFiber10Prefix8 ++ [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23]
      (chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 8) ttFiber10State8_in_pass1_prefix8
  rw [show ttFiber10Prefix24 = ttFiber10Prefix23 ++ [ttFiber10StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 24) []
    (chainClosureStep ttWord ttFiber10Prefix23 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 8) hparentBefore ttFiber10ReverseSingleStep24

theorem ttFiber10State24_in_pass1_full :
    ttFiber10StateAt 24 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix24 ++ [ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix24 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 24) ttFiber10State24_in_pass1_prefix24

theorem ttFiber10State25_in_pass1_prefix25 :
    ttFiber10StateAt 25 ∈ chainClosureStep ttWord ttFiber10Prefix25 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 9 ∈
      chainClosureStep ttWord ttFiber10Prefix24 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix24 = ttFiber10Prefix9 ++ [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24]
      (chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 9) ttFiber10State9_in_pass1_prefix9
  rw [show ttFiber10Prefix25 = ttFiber10Prefix24 ++ [ttFiber10StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 25) []
    (chainClosureStep ttWord ttFiber10Prefix24 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 9) hparentBefore ttFiber10ReverseSingleStep25

theorem ttFiber10State25_in_pass1_full :
    ttFiber10StateAt 25 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix25 ++ [ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix25 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 25) ttFiber10State25_in_pass1_prefix25

theorem ttFiber10State26_in_pass1_prefix26 :
    ttFiber10StateAt 26 ∈ chainClosureStep ttWord ttFiber10Prefix26 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 10 ∈
      chainClosureStep ttWord ttFiber10Prefix25 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix25 = ttFiber10Prefix10 ++ [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25]
      (chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 10) ttFiber10State10_in_pass1_prefix10
  rw [show ttFiber10Prefix26 = ttFiber10Prefix25 ++ [ttFiber10StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 26) []
    (chainClosureStep ttWord ttFiber10Prefix25 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 10) hparentBefore ttFiber10ReverseSingleStep26

theorem ttFiber10State26_in_pass1_full :
    ttFiber10StateAt 26 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix26 ++ [ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix26 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 26) ttFiber10State26_in_pass1_prefix26

theorem ttFiber10State27_in_pass1_prefix27 :
    ttFiber10StateAt 27 ∈ chainClosureStep ttWord ttFiber10Prefix27 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 11 ∈
      chainClosureStep ttWord ttFiber10Prefix26 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix26 = ttFiber10Prefix11 ++ [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26]
      (chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 11) ttFiber10State11_in_pass1_prefix11
  rw [show ttFiber10Prefix27 = ttFiber10Prefix26 ++ [ttFiber10StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 27) []
    (chainClosureStep ttWord ttFiber10Prefix26 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 11) hparentBefore ttFiber10ReverseSingleStep27

theorem ttFiber10State27_in_pass1_full :
    ttFiber10StateAt 27 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix27 ++ [ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix27 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 27) ttFiber10State27_in_pass1_prefix27

theorem ttFiber10State28_in_pass1_prefix28 :
    ttFiber10StateAt 28 ∈ chainClosureStep ttWord ttFiber10Prefix28 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 24 ∈
      chainClosureStep ttWord ttFiber10Prefix27 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix27 = ttFiber10Prefix24 ++ [ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27]
      (chainClosureStep ttWord ttFiber10Prefix24 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 24) ttFiber10State24_in_pass1_prefix24
  rw [show ttFiber10Prefix28 = ttFiber10Prefix27 ++ [ttFiber10StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 28) []
    (chainClosureStep ttWord ttFiber10Prefix27 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 24) hparentBefore ttFiber10ReverseSingleStep28

theorem ttFiber10State28_in_pass1_full :
    ttFiber10StateAt 28 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix28 ++ [ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix28 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 28) ttFiber10State28_in_pass1_prefix28

theorem ttFiber10State29_in_pass1_prefix29 :
    ttFiber10StateAt 29 ∈ chainClosureStep ttWord ttFiber10Prefix29 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 25 ∈
      chainClosureStep ttWord ttFiber10Prefix28 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix28 = ttFiber10Prefix25 ++ [ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28]
      (chainClosureStep ttWord ttFiber10Prefix25 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 25) ttFiber10State25_in_pass1_prefix25
  rw [show ttFiber10Prefix29 = ttFiber10Prefix28 ++ [ttFiber10StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 29) []
    (chainClosureStep ttWord ttFiber10Prefix28 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 25) hparentBefore ttFiber10ReverseSingleStep29

theorem ttFiber10State29_in_pass1_full :
    ttFiber10StateAt 29 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix29 ++ [ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix29 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 29) ttFiber10State29_in_pass1_prefix29

theorem ttFiber10State30_in_pass1_prefix30 :
    ttFiber10StateAt 30 ∈ chainClosureStep ttWord ttFiber10Prefix30 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 14 ∈
      chainClosureStep ttWord ttFiber10Prefix29 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix29 = ttFiber10Prefix14 ++ [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29]
      (chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 14) ttFiber10State14_in_pass1_prefix14
  rw [show ttFiber10Prefix30 = ttFiber10Prefix29 ++ [ttFiber10StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 30) []
    (chainClosureStep ttWord ttFiber10Prefix29 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 14) hparentBefore ttFiber10ReverseSingleStep30

theorem ttFiber10State30_in_pass1_full :
    ttFiber10StateAt 30 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix30 ++ [ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix30 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 30) ttFiber10State30_in_pass1_prefix30

theorem ttFiber10State31_in_pass1_prefix31 :
    ttFiber10StateAt 31 ∈ chainClosureStep ttWord ttFiber10Prefix31 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 15 ∈
      chainClosureStep ttWord ttFiber10Prefix30 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix30 = ttFiber10Prefix15 ++ [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30]
      (chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 15) ttFiber10State15_in_pass1_prefix15
  rw [show ttFiber10Prefix31 = ttFiber10Prefix30 ++ [ttFiber10StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 31) []
    (chainClosureStep ttWord ttFiber10Prefix30 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 15) hparentBefore ttFiber10ReverseSingleStep31

theorem ttFiber10State31_in_pass1_full :
    ttFiber10StateAt 31 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix31 ++ [ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix31 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 31) ttFiber10State31_in_pass1_prefix31

theorem ttFiber10State34_in_pass1_prefix34 :
    ttFiber10StateAt 34 ∈ chainClosureStep ttWord ttFiber10Prefix34 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 22 ∈
      chainClosureStep ttWord ttFiber10Prefix33 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix33 = ttFiber10Prefix22 ++ [ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33]
      (chainClosureStep ttWord ttFiber10Prefix22 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 22) ttFiber10State22_in_pass1_prefix22
  rw [show ttFiber10Prefix34 = ttFiber10Prefix33 ++ [ttFiber10StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 34) []
    (chainClosureStep ttWord ttFiber10Prefix33 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 22) hparentBefore ttFiber10ReverseSingleStep34

theorem ttFiber10State34_in_pass1_full :
    ttFiber10StateAt 34 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix34 ++ [ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix34 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 34) ttFiber10State34_in_pass1_prefix34

theorem ttFiber10State35_in_pass1_prefix35 :
    ttFiber10StateAt 35 ∈ chainClosureStep ttWord ttFiber10Prefix35 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 23 ∈
      chainClosureStep ttWord ttFiber10Prefix34 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix34 = ttFiber10Prefix23 ++ [ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34]
      (chainClosureStep ttWord ttFiber10Prefix23 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 23) ttFiber10State23_in_pass1_prefix23
  rw [show ttFiber10Prefix35 = ttFiber10Prefix34 ++ [ttFiber10StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 35) []
    (chainClosureStep ttWord ttFiber10Prefix34 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 23) hparentBefore ttFiber10ReverseSingleStep35

theorem ttFiber10State35_in_pass1_full :
    ttFiber10StateAt 35 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix35 ++ [ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix35 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 35) ttFiber10State35_in_pass1_prefix35

theorem ttFiber10State36_in_pass1_prefix36 :
    ttFiber10StateAt 36 ∈ chainClosureStep ttWord ttFiber10Prefix36 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 18 ∈
      chainClosureStep ttWord ttFiber10Prefix35 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix35 = ttFiber10Prefix18 ++ [ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35]
      (chainClosureStep ttWord ttFiber10Prefix18 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 18) ttFiber10State18_in_pass1_prefix18
  rw [show ttFiber10Prefix36 = ttFiber10Prefix35 ++ [ttFiber10StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 36) []
    (chainClosureStep ttWord ttFiber10Prefix35 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 18) hparentBefore ttFiber10ReverseSingleStep36

theorem ttFiber10State36_in_pass1_full :
    ttFiber10StateAt 36 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix36 ++ [ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix36 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 36) ttFiber10State36_in_pass1_prefix36

theorem ttFiber10State38_in_pass1_prefix38 :
    ttFiber10StateAt 38 ∈ chainClosureStep ttWord ttFiber10Prefix38 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 17 ∈
      chainClosureStep ttWord ttFiber10Prefix37 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix37 = ttFiber10Prefix17 ++ [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37]
      (chainClosureStep ttWord ttFiber10Prefix17 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 17) ttFiber10State17_in_pass1_prefix17
  rw [show ttFiber10Prefix38 = ttFiber10Prefix37 ++ [ttFiber10StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 38) []
    (chainClosureStep ttWord ttFiber10Prefix37 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 17) hparentBefore ttFiber10ReverseSingleStep38

theorem ttFiber10State38_in_pass1_full :
    ttFiber10StateAt 38 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix38 ++ [ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix38 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 38) ttFiber10State38_in_pass1_prefix38

theorem ttFiber10State39_in_pass1_prefix39 :
    ttFiber10StateAt 39 ∈ chainClosureStep ttWord ttFiber10Prefix39 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 16 ∈
      chainClosureStep ttWord ttFiber10Prefix38 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix38 = ttFiber10Prefix16 ++ [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38]
      (chainClosureStep ttWord ttFiber10Prefix16 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 16) ttFiber10State16_in_pass1_prefix16
  rw [show ttFiber10Prefix39 = ttFiber10Prefix38 ++ [ttFiber10StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 39) []
    (chainClosureStep ttWord ttFiber10Prefix38 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 16) hparentBefore ttFiber10ReverseSingleStep39

theorem ttFiber10State39_in_pass1_full :
    ttFiber10StateAt 39 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix39 ++ [ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix39 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 39) ttFiber10State39_in_pass1_prefix39

theorem ttFiber10State48_in_pass1_prefix48 :
    ttFiber10StateAt 48 ∈ chainClosureStep ttWord ttFiber10Prefix48 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 8 ∈
      chainClosureStep ttWord ttFiber10Prefix47 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix47 = ttFiber10Prefix8 ++ [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47]
      (chainClosureStep ttWord ttFiber10Prefix8 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 8) ttFiber10State8_in_pass1_prefix8
  rw [show ttFiber10Prefix48 = ttFiber10Prefix47 ++ [ttFiber10StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 48) []
    (chainClosureStep ttWord ttFiber10Prefix47 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 8) hparentBefore ttFiber10ReverseSingleStep48

theorem ttFiber10State48_in_pass1_full :
    ttFiber10StateAt 48 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix48 ++ [ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix48 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 48) ttFiber10State48_in_pass1_prefix48

theorem ttFiber10State49_in_pass1_prefix49 :
    ttFiber10StateAt 49 ∈ chainClosureStep ttWord ttFiber10Prefix49 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 9 ∈
      chainClosureStep ttWord ttFiber10Prefix48 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix48 = ttFiber10Prefix9 ++ [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48]
      (chainClosureStep ttWord ttFiber10Prefix9 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 9) ttFiber10State9_in_pass1_prefix9
  rw [show ttFiber10Prefix49 = ttFiber10Prefix48 ++ [ttFiber10StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 49) []
    (chainClosureStep ttWord ttFiber10Prefix48 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 9) hparentBefore ttFiber10ReverseSingleStep49

theorem ttFiber10State49_in_pass1_full :
    ttFiber10StateAt 49 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix49 ++ [ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix49 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 49) ttFiber10State49_in_pass1_prefix49

theorem ttFiber10State50_in_pass1_prefix50 :
    ttFiber10StateAt 50 ∈ chainClosureStep ttWord ttFiber10Prefix50 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 10 ∈
      chainClosureStep ttWord ttFiber10Prefix49 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix49 = ttFiber10Prefix10 ++ [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49]
      (chainClosureStep ttWord ttFiber10Prefix10 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 10) ttFiber10State10_in_pass1_prefix10
  rw [show ttFiber10Prefix50 = ttFiber10Prefix49 ++ [ttFiber10StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 50) []
    (chainClosureStep ttWord ttFiber10Prefix49 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 10) hparentBefore ttFiber10ReverseSingleStep50

theorem ttFiber10State50_in_pass1_full :
    ttFiber10StateAt 50 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix50 ++ [ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix50 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 50) ttFiber10State50_in_pass1_prefix50

theorem ttFiber10State51_in_pass1_prefix51 :
    ttFiber10StateAt 51 ∈ chainClosureStep ttWord ttFiber10Prefix51 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 11 ∈
      chainClosureStep ttWord ttFiber10Prefix50 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix50 = ttFiber10Prefix11 ++ [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50]
      (chainClosureStep ttWord ttFiber10Prefix11 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 11) ttFiber10State11_in_pass1_prefix11
  rw [show ttFiber10Prefix51 = ttFiber10Prefix50 ++ [ttFiber10StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 51) []
    (chainClosureStep ttWord ttFiber10Prefix50 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 11) hparentBefore ttFiber10ReverseSingleStep51

theorem ttFiber10State51_in_pass1_full :
    ttFiber10StateAt 51 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix51 ++ [ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix51 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 51) ttFiber10State51_in_pass1_prefix51

theorem ttFiber10State52_in_pass1_prefix52 :
    ttFiber10StateAt 52 ∈ chainClosureStep ttWord ttFiber10Prefix52 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 12 ∈
      chainClosureStep ttWord ttFiber10Prefix51 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix51 = ttFiber10Prefix12 ++ [ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51]
      (chainClosureStep ttWord ttFiber10Prefix12 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 12) ttFiber10State12_in_pass1_prefix12
  rw [show ttFiber10Prefix52 = ttFiber10Prefix51 ++ [ttFiber10StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 52) []
    (chainClosureStep ttWord ttFiber10Prefix51 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 12) hparentBefore ttFiber10ReverseSingleStep52

theorem ttFiber10State52_in_pass1_full :
    ttFiber10StateAt 52 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix52 ++ [ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix52 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 52) ttFiber10State52_in_pass1_prefix52

theorem ttFiber10State54_in_pass1_prefix54 :
    ttFiber10StateAt 54 ∈ chainClosureStep ttWord ttFiber10Prefix54 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 14 ∈
      chainClosureStep ttWord ttFiber10Prefix53 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix53 = ttFiber10Prefix14 ++ [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53]
      (chainClosureStep ttWord ttFiber10Prefix14 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 14) ttFiber10State14_in_pass1_prefix14
  rw [show ttFiber10Prefix54 = ttFiber10Prefix53 ++ [ttFiber10StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 54) []
    (chainClosureStep ttWord ttFiber10Prefix53 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 14) hparentBefore ttFiber10ReverseSingleStep54

theorem ttFiber10State54_in_pass1_full :
    ttFiber10StateAt 54 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix54 ++ [ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix54 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 54) ttFiber10State54_in_pass1_prefix54

theorem ttFiber10State55_in_pass1_prefix55 :
    ttFiber10StateAt 55 ∈ chainClosureStep ttWord ttFiber10Prefix55 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 15 ∈
      chainClosureStep ttWord ttFiber10Prefix54 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix54 = ttFiber10Prefix15 ++ [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54]
      (chainClosureStep ttWord ttFiber10Prefix15 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 15) ttFiber10State15_in_pass1_prefix15
  rw [show ttFiber10Prefix55 = ttFiber10Prefix54 ++ [ttFiber10StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 55) []
    (chainClosureStep ttWord ttFiber10Prefix54 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 15) hparentBefore ttFiber10ReverseSingleStep55

theorem ttFiber10State55_in_pass1_full :
    ttFiber10StateAt 55 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix55 ++ [ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix55 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 55) ttFiber10State55_in_pass1_prefix55

theorem ttFiber10State56_in_pass1_prefix56 :
    ttFiber10StateAt 56 ∈ chainClosureStep ttWord ttFiber10Prefix56 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 0 ∈
      chainClosureStep ttWord ttFiber10Prefix55 ([ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix55
      ([ttFiber10StateAt 0]) (ttFiber10StateAt 0) ttFiber10State0_in_pass0_full
  rw [show ttFiber10Prefix56 = ttFiber10Prefix55 ++ [ttFiber10StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 56) []
    (chainClosureStep ttWord ttFiber10Prefix55 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 0) hparentBefore ttFiber10ReverseSingleStep56

theorem ttFiber10State56_in_pass1_full :
    ttFiber10StateAt 56 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix56 ++ [ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix56 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 56) ttFiber10State56_in_pass1_prefix56

theorem ttFiber10State57_in_pass1_prefix57 :
    ttFiber10StateAt 57 ∈ chainClosureStep ttWord ttFiber10Prefix57 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 1 ∈
      chainClosureStep ttWord ttFiber10Prefix56 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix56 = ttFiber10Prefix1 ++ [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 2, ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56]
      (chainClosureStep ttWord ttFiber10Prefix1 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 1) ttFiber10State1_in_pass1_prefix1
  rw [show ttFiber10Prefix57 = ttFiber10Prefix56 ++ [ttFiber10StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 57) []
    (chainClosureStep ttWord ttFiber10Prefix56 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 1) hparentBefore ttFiber10ReverseSingleStep57

theorem ttFiber10State57_in_pass1_full :
    ttFiber10StateAt 57 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix57 ++ [ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix57 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 57) ttFiber10State57_in_pass1_prefix57

theorem ttFiber10State58_in_pass1_prefix58 :
    ttFiber10StateAt 58 ∈ chainClosureStep ttWord ttFiber10Prefix58 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 2 ∈
      chainClosureStep ttWord ttFiber10Prefix57 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix57 = ttFiber10Prefix2 ++ [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 3, ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57]
      (chainClosureStep ttWord ttFiber10Prefix2 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 2) ttFiber10State2_in_pass1_prefix2
  rw [show ttFiber10Prefix58 = ttFiber10Prefix57 ++ [ttFiber10StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 58) []
    (chainClosureStep ttWord ttFiber10Prefix57 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 2) hparentBefore ttFiber10ReverseSingleStep58

theorem ttFiber10State58_in_pass1_full :
    ttFiber10StateAt 58 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix58 ++ [ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix58 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 58) ttFiber10State58_in_pass1_prefix58

theorem ttFiber10State59_in_pass1_prefix59 :
    ttFiber10StateAt 59 ∈ chainClosureStep ttWord ttFiber10Prefix59 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 3 ∈
      chainClosureStep ttWord ttFiber10Prefix58 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix58 = ttFiber10Prefix3 ++ [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 4, ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58]
      (chainClosureStep ttWord ttFiber10Prefix3 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 3) ttFiber10State3_in_pass1_prefix3
  rw [show ttFiber10Prefix59 = ttFiber10Prefix58 ++ [ttFiber10StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 59) []
    (chainClosureStep ttWord ttFiber10Prefix58 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 3) hparentBefore ttFiber10ReverseSingleStep59

theorem ttFiber10State59_in_pass1_full :
    ttFiber10StateAt 59 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix59 ++ [ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix59 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 59) ttFiber10State59_in_pass1_prefix59

theorem ttFiber10State60_in_pass1_prefix60 :
    ttFiber10StateAt 60 ∈ chainClosureStep ttWord ttFiber10Prefix60 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 4 ∈
      chainClosureStep ttWord ttFiber10Prefix59 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix59 = ttFiber10Prefix4 ++ [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 5, ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59]
      (chainClosureStep ttWord ttFiber10Prefix4 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 4) ttFiber10State4_in_pass1_prefix4
  rw [show ttFiber10Prefix60 = ttFiber10Prefix59 ++ [ttFiber10StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 60) []
    (chainClosureStep ttWord ttFiber10Prefix59 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 4) hparentBefore ttFiber10ReverseSingleStep60

theorem ttFiber10State60_in_pass1_full :
    ttFiber10StateAt 60 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix60 ++ [ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix60 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 60) ttFiber10State60_in_pass1_prefix60

theorem ttFiber10State62_in_pass1_prefix62 :
    ttFiber10StateAt 62 ∈ chainClosureStep ttWord ttFiber10Prefix62 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 6 ∈
      chainClosureStep ttWord ttFiber10Prefix61 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix61 = ttFiber10Prefix6 ++ [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61]
      (chainClosureStep ttWord ttFiber10Prefix6 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 6) ttFiber10State6_in_pass1_prefix6
  rw [show ttFiber10Prefix62 = ttFiber10Prefix61 ++ [ttFiber10StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 62) []
    (chainClosureStep ttWord ttFiber10Prefix61 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 6) hparentBefore ttFiber10ReverseSingleStep62

theorem ttFiber10State62_in_pass1_full :
    ttFiber10StateAt 62 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix62 ++ [ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix62 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 62) ttFiber10State62_in_pass1_prefix62

theorem ttFiber10State63_in_pass1_prefix63 :
    ttFiber10StateAt 63 ∈ chainClosureStep ttWord ttFiber10Prefix63 ([ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 7 ∈
      chainClosureStep ttWord ttFiber10Prefix62 ([ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix62 = ttFiber10Prefix7 ++ [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62]
      (chainClosureStep ttWord ttFiber10Prefix7 ([ttFiber10StateAt 0]))
      (ttFiber10StateAt 7) ttFiber10State7_in_pass1_prefix7
  rw [show ttFiber10Prefix63 = ttFiber10Prefix62 ++ [ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 63) []
    (chainClosureStep ttWord ttFiber10Prefix62 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 7) hparentBefore ttFiber10ReverseSingleStep63

theorem ttFiber10State63_in_pass1_full :
    ttFiber10StateAt 63 ∈ chainClosureStep ttWord ttFiber10DirectStates ([ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber10Prefix63 ([ttFiber10StateAt 0]))
    (ttFiber10StateAt 63) ttFiber10State63_in_pass1_prefix63

theorem ttFiber10State5_in_pass2_prefix5 :
    ttFiber10StateAt 5 ∈ chainClosureStep ttWord ttFiber10Prefix5 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 7 ∈
      chainClosureStep ttWord ttFiber10Prefix4 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix4
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 7) ttFiber10State7_in_pass1_full
  rw [show ttFiber10Prefix5 = ttFiber10Prefix4 ++ [ttFiber10StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 5) []
    (chainClosureStep ttWord ttFiber10Prefix4 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 7) hparentBefore ttFiber10ReverseSingleStep5

theorem ttFiber10State5_in_pass2_full :
    ttFiber10StateAt 5 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix5 ++ [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix5 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 5) ttFiber10State5_in_pass2_prefix5

theorem ttFiber10State13_in_pass2_prefix13 :
    ttFiber10StateAt 13 ∈ chainClosureStep ttWord ttFiber10Prefix13 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 5 ∈
      chainClosureStep ttWord ttFiber10Prefix12 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix12 = ttFiber10Prefix5 ++ [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12]
      (chainClosureStep ttWord ttFiber10Prefix5 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 5) ttFiber10State5_in_pass2_prefix5
  rw [show ttFiber10Prefix13 = ttFiber10Prefix12 ++ [ttFiber10StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 13) []
    (chainClosureStep ttWord ttFiber10Prefix12 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 5) hparentBefore ttFiber10ReverseSingleStep13

theorem ttFiber10State13_in_pass2_full :
    ttFiber10StateAt 13 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix13 ++ [ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix13 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 13) ttFiber10State13_in_pass2_prefix13

theorem ttFiber10State32_in_pass2_prefix32 :
    ttFiber10StateAt 32 ∈ chainClosureStep ttWord ttFiber10Prefix32 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 48 ∈
      chainClosureStep ttWord ttFiber10Prefix31 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix31
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 48) ttFiber10State48_in_pass1_full
  rw [show ttFiber10Prefix32 = ttFiber10Prefix31 ++ [ttFiber10StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 32) []
    (chainClosureStep ttWord ttFiber10Prefix31 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 48) hparentBefore ttFiber10ReverseSingleStep32

theorem ttFiber10State32_in_pass2_full :
    ttFiber10StateAt 32 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix32 ++ [ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix32 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 32) ttFiber10State32_in_pass2_prefix32

theorem ttFiber10State33_in_pass2_prefix33 :
    ttFiber10StateAt 33 ∈ chainClosureStep ttWord ttFiber10Prefix33 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 49 ∈
      chainClosureStep ttWord ttFiber10Prefix32 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix32
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 49) ttFiber10State49_in_pass1_full
  rw [show ttFiber10Prefix33 = ttFiber10Prefix32 ++ [ttFiber10StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 33) []
    (chainClosureStep ttWord ttFiber10Prefix32 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 49) hparentBefore ttFiber10ReverseSingleStep33

theorem ttFiber10State33_in_pass2_full :
    ttFiber10StateAt 33 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix33 ++ [ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix33 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 33) ttFiber10State33_in_pass2_prefix33

theorem ttFiber10State37_in_pass2_prefix37 :
    ttFiber10StateAt 37 ∈ chainClosureStep ttWord ttFiber10Prefix37 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 39 ∈
      chainClosureStep ttWord ttFiber10Prefix36 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix36
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 39) ttFiber10State39_in_pass1_full
  rw [show ttFiber10Prefix37 = ttFiber10Prefix36 ++ [ttFiber10StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 37) []
    (chainClosureStep ttWord ttFiber10Prefix36 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 39) hparentBefore ttFiber10ReverseSingleStep37

theorem ttFiber10State37_in_pass2_full :
    ttFiber10StateAt 37 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix37 ++ [ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix37 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 37) ttFiber10State37_in_pass2_prefix37

theorem ttFiber10State40_in_pass2_prefix40 :
    ttFiber10StateAt 40 ∈ chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 56 ∈
      chainClosureStep ttWord ttFiber10Prefix39 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix39
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 56) ttFiber10State56_in_pass1_full
  rw [show ttFiber10Prefix40 = ttFiber10Prefix39 ++ [ttFiber10StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 40) []
    (chainClosureStep ttWord ttFiber10Prefix39 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 56) hparentBefore ttFiber10ReverseSingleStep40

theorem ttFiber10State40_in_pass2_full :
    ttFiber10StateAt 40 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix40 ++ [ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 40) ttFiber10State40_in_pass2_prefix40

theorem ttFiber10State41_in_pass2_prefix41 :
    ttFiber10StateAt 41 ∈ chainClosureStep ttWord ttFiber10Prefix41 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 57 ∈
      chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix40
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 57) ttFiber10State57_in_pass1_full
  rw [show ttFiber10Prefix41 = ttFiber10Prefix40 ++ [ttFiber10StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 41) []
    (chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 57) hparentBefore ttFiber10ReverseSingleStep41

theorem ttFiber10State41_in_pass2_full :
    ttFiber10StateAt 41 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix41 ++ [ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix41 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 41) ttFiber10State41_in_pass2_prefix41

theorem ttFiber10State42_in_pass2_prefix42 :
    ttFiber10StateAt 42 ∈ chainClosureStep ttWord ttFiber10Prefix42 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 58 ∈
      chainClosureStep ttWord ttFiber10Prefix41 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix41
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 58) ttFiber10State58_in_pass1_full
  rw [show ttFiber10Prefix42 = ttFiber10Prefix41 ++ [ttFiber10StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 42) []
    (chainClosureStep ttWord ttFiber10Prefix41 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 58) hparentBefore ttFiber10ReverseSingleStep42

theorem ttFiber10State42_in_pass2_full :
    ttFiber10StateAt 42 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix42 ++ [ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix42 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 42) ttFiber10State42_in_pass2_prefix42

theorem ttFiber10State43_in_pass2_prefix43 :
    ttFiber10StateAt 43 ∈ chainClosureStep ttWord ttFiber10Prefix43 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 40 ∈
      chainClosureStep ttWord ttFiber10Prefix42 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix42 = ttFiber10Prefix40 ++ [ttFiber10StateAt 41, ttFiber10StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 41, ttFiber10StateAt 42]
      (chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 40) ttFiber10State40_in_pass2_prefix40
  rw [show ttFiber10Prefix43 = ttFiber10Prefix42 ++ [ttFiber10StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 43) []
    (chainClosureStep ttWord ttFiber10Prefix42 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 40) hparentBefore ttFiber10ReverseSingleStep43

theorem ttFiber10State43_in_pass2_full :
    ttFiber10StateAt 43 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix43 ++ [ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix43 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 43) ttFiber10State43_in_pass2_prefix43

theorem ttFiber10State44_in_pass2_prefix44 :
    ttFiber10StateAt 44 ∈ chainClosureStep ttWord ttFiber10Prefix44 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 40 ∈
      chainClosureStep ttWord ttFiber10Prefix43 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix43 = ttFiber10Prefix40 ++ [ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43]
      (chainClosureStep ttWord ttFiber10Prefix40 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 40) ttFiber10State40_in_pass2_prefix40
  rw [show ttFiber10Prefix44 = ttFiber10Prefix43 ++ [ttFiber10StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 44) []
    (chainClosureStep ttWord ttFiber10Prefix43 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 40) hparentBefore ttFiber10ReverseSingleStep44

theorem ttFiber10State44_in_pass2_full :
    ttFiber10StateAt 44 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix44 ++ [ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix44 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 44) ttFiber10State44_in_pass2_prefix44

theorem ttFiber10State45_in_pass2_prefix45 :
    ttFiber10StateAt 45 ∈ chainClosureStep ttWord ttFiber10Prefix45 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 41 ∈
      chainClosureStep ttWord ttFiber10Prefix44 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix44 = ttFiber10Prefix41 ++ [ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44]
      (chainClosureStep ttWord ttFiber10Prefix41 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 41) ttFiber10State41_in_pass2_prefix41
  rw [show ttFiber10Prefix45 = ttFiber10Prefix44 ++ [ttFiber10StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 45) []
    (chainClosureStep ttWord ttFiber10Prefix44 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 41) hparentBefore ttFiber10ReverseSingleStep45

theorem ttFiber10State45_in_pass2_full :
    ttFiber10StateAt 45 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix45 ++ [ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix45 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 45) ttFiber10State45_in_pass2_prefix45

theorem ttFiber10State46_in_pass2_prefix46 :
    ttFiber10StateAt 46 ∈ chainClosureStep ttWord ttFiber10Prefix46 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 62 ∈
      chainClosureStep ttWord ttFiber10Prefix45 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix45
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 62) ttFiber10State62_in_pass1_full
  rw [show ttFiber10Prefix46 = ttFiber10Prefix45 ++ [ttFiber10StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 46) []
    (chainClosureStep ttWord ttFiber10Prefix45 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 62) hparentBefore ttFiber10ReverseSingleStep46

theorem ttFiber10State46_in_pass2_full :
    ttFiber10StateAt 46 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix46 ++ [ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix46 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 46) ttFiber10State46_in_pass2_prefix46

theorem ttFiber10State47_in_pass2_prefix47 :
    ttFiber10StateAt 47 ∈ chainClosureStep ttWord ttFiber10Prefix47 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 63 ∈
      chainClosureStep ttWord ttFiber10Prefix46 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber10Prefix46
      (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) (ttFiber10StateAt 63) ttFiber10State63_in_pass1_full
  rw [show ttFiber10Prefix47 = ttFiber10Prefix46 ++ [ttFiber10StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 47) []
    (chainClosureStep ttWord ttFiber10Prefix46 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 63) hparentBefore ttFiber10ReverseSingleStep47

theorem ttFiber10State47_in_pass2_full :
    ttFiber10StateAt 47 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix47 ++ [ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix47 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 47) ttFiber10State47_in_pass2_prefix47

theorem ttFiber10State53_in_pass2_prefix53 :
    ttFiber10StateAt 53 ∈ chainClosureStep ttWord ttFiber10Prefix53 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 13 ∈
      chainClosureStep ttWord ttFiber10Prefix52 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix52 = ttFiber10Prefix13 ++ [ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52]
      (chainClosureStep ttWord ttFiber10Prefix13 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 13) ttFiber10State13_in_pass2_prefix13
  rw [show ttFiber10Prefix53 = ttFiber10Prefix52 ++ [ttFiber10StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 53) []
    (chainClosureStep ttWord ttFiber10Prefix52 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 13) hparentBefore ttFiber10ReverseSingleStep53

theorem ttFiber10State53_in_pass2_full :
    ttFiber10StateAt 53 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix53 ++ [ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60, ttFiber10StateAt 61, ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix53 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 53) ttFiber10State53_in_pass2_prefix53

theorem ttFiber10State61_in_pass2_prefix61 :
    ttFiber10StateAt 61 ∈ chainClosureStep ttWord ttFiber10Prefix61 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  have hparentBefore : ttFiber10StateAt 5 ∈
      chainClosureStep ttWord ttFiber10Prefix60 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
    rw [show ttFiber10Prefix60 = ttFiber10Prefix5 ++ [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 6, ttFiber10StateAt 7, ttFiber10StateAt 8, ttFiber10StateAt 9, ttFiber10StateAt 10, ttFiber10StateAt 11, ttFiber10StateAt 12, ttFiber10StateAt 13, ttFiber10StateAt 14, ttFiber10StateAt 15, ttFiber10StateAt 16, ttFiber10StateAt 17, ttFiber10StateAt 18, ttFiber10StateAt 19, ttFiber10StateAt 20, ttFiber10StateAt 21, ttFiber10StateAt 22, ttFiber10StateAt 23, ttFiber10StateAt 24, ttFiber10StateAt 25, ttFiber10StateAt 26, ttFiber10StateAt 27, ttFiber10StateAt 28, ttFiber10StateAt 29, ttFiber10StateAt 30, ttFiber10StateAt 31, ttFiber10StateAt 32, ttFiber10StateAt 33, ttFiber10StateAt 34, ttFiber10StateAt 35, ttFiber10StateAt 36, ttFiber10StateAt 37, ttFiber10StateAt 38, ttFiber10StateAt 39, ttFiber10StateAt 40, ttFiber10StateAt 41, ttFiber10StateAt 42, ttFiber10StateAt 43, ttFiber10StateAt 44, ttFiber10StateAt 45, ttFiber10StateAt 46, ttFiber10StateAt 47, ttFiber10StateAt 48, ttFiber10StateAt 49, ttFiber10StateAt 50, ttFiber10StateAt 51, ttFiber10StateAt 52, ttFiber10StateAt 53, ttFiber10StateAt 54, ttFiber10StateAt 55, ttFiber10StateAt 56, ttFiber10StateAt 57, ttFiber10StateAt 58, ttFiber10StateAt 59, ttFiber10StateAt 60]
      (chainClosureStep ttWord ttFiber10Prefix5 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
      (ttFiber10StateAt 5) ttFiber10State5_in_pass2_prefix5
  rw [show ttFiber10Prefix61 = ttFiber10Prefix60 ++ [ttFiber10StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber10StateAt 61) []
    (chainClosureStep ttWord ttFiber10Prefix60 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 5) hparentBefore ttFiber10ReverseSingleStep61

theorem ttFiber10State61_in_pass2_full :
    ttFiber10StateAt 61 ∈ chainClosureStep ttWord ttFiber10DirectStates (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]) := by
  rw [show ttFiber10DirectStates = ttFiber10Prefix61 ++ [ttFiber10StateAt 62, ttFiber10StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber10StateAt 62, ttFiber10StateAt 63]
    (chainClosureStep ttWord ttFiber10Prefix61 (chainClosureStep ttWord ttFiber10DirectStates [ttFiber10StateAt 0]))
    (ttFiber10StateAt 61) ttFiber10State61_in_pass2_prefix61

theorem ttFiber10State0_in_close :
    ttFiber10StateAt 0 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber10DirectStates
    ttFiber10DirectStates.length [ttFiber10StateAt 0] (ttFiber10StateAt 0) (by simp)

theorem ttFiber10State1_in_close :
    ttFiber10StateAt 1 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 1 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 1) ttFiber10State1_in_pass1_full

theorem ttFiber10State2_in_close :
    ttFiber10StateAt 2 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 2 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 2) ttFiber10State2_in_pass1_full

theorem ttFiber10State3_in_close :
    ttFiber10StateAt 3 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 3 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 3) ttFiber10State3_in_pass1_full

theorem ttFiber10State4_in_close :
    ttFiber10StateAt 4 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 4 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 4) ttFiber10State4_in_pass1_full

theorem ttFiber10State5_in_close :
    ttFiber10StateAt 5 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 5 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 5) ttFiber10FirstPassGrows
    ttFiber10State5_in_pass2_full

theorem ttFiber10State6_in_close :
    ttFiber10StateAt 6 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 6 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 6) ttFiber10State6_in_pass1_full

theorem ttFiber10State7_in_close :
    ttFiber10StateAt 7 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 7 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 7) ttFiber10State7_in_pass1_full

theorem ttFiber10State8_in_close :
    ttFiber10StateAt 8 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 8 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 8) ttFiber10State8_in_pass1_full

theorem ttFiber10State9_in_close :
    ttFiber10StateAt 9 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 9 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 9) ttFiber10State9_in_pass1_full

theorem ttFiber10State10_in_close :
    ttFiber10StateAt 10 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 10 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 10) ttFiber10State10_in_pass1_full

theorem ttFiber10State11_in_close :
    ttFiber10StateAt 11 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 11 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 11) ttFiber10State11_in_pass1_full

theorem ttFiber10State12_in_close :
    ttFiber10StateAt 12 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 12 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 12) ttFiber10State12_in_pass1_full

theorem ttFiber10State13_in_close :
    ttFiber10StateAt 13 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 13 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 13) ttFiber10FirstPassGrows
    ttFiber10State13_in_pass2_full

theorem ttFiber10State14_in_close :
    ttFiber10StateAt 14 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 14 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 14) ttFiber10State14_in_pass1_full

theorem ttFiber10State15_in_close :
    ttFiber10StateAt 15 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 15 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 15) ttFiber10State15_in_pass1_full

theorem ttFiber10State16_in_close :
    ttFiber10StateAt 16 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 16 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 16) ttFiber10State16_in_pass1_full

theorem ttFiber10State17_in_close :
    ttFiber10StateAt 17 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 17 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 17) ttFiber10State17_in_pass1_full

theorem ttFiber10State18_in_close :
    ttFiber10StateAt 18 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 18 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 18) ttFiber10State18_in_pass1_full

theorem ttFiber10State19_in_close :
    ttFiber10StateAt 19 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 19 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 19) ttFiber10State19_in_pass1_full

theorem ttFiber10State20_in_close :
    ttFiber10StateAt 20 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 20 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 20) ttFiber10State20_in_pass1_full

theorem ttFiber10State21_in_close :
    ttFiber10StateAt 21 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 21 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 21) ttFiber10State21_in_pass1_full

theorem ttFiber10State22_in_close :
    ttFiber10StateAt 22 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 22 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 22) ttFiber10State22_in_pass1_full

theorem ttFiber10State23_in_close :
    ttFiber10StateAt 23 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 23 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 23) ttFiber10State23_in_pass1_full

theorem ttFiber10State24_in_close :
    ttFiber10StateAt 24 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 24 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 24) ttFiber10State24_in_pass1_full

theorem ttFiber10State25_in_close :
    ttFiber10StateAt 25 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 25 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 25) ttFiber10State25_in_pass1_full

theorem ttFiber10State26_in_close :
    ttFiber10StateAt 26 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 26 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 26) ttFiber10State26_in_pass1_full

theorem ttFiber10State27_in_close :
    ttFiber10StateAt 27 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 27 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 27) ttFiber10State27_in_pass1_full

theorem ttFiber10State28_in_close :
    ttFiber10StateAt 28 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 28 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 28) ttFiber10State28_in_pass1_full

theorem ttFiber10State29_in_close :
    ttFiber10StateAt 29 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 29 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 29) ttFiber10State29_in_pass1_full

theorem ttFiber10State30_in_close :
    ttFiber10StateAt 30 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 30 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 30) ttFiber10State30_in_pass1_full

theorem ttFiber10State31_in_close :
    ttFiber10StateAt 31 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 31 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 31) ttFiber10State31_in_pass1_full

theorem ttFiber10State32_in_close :
    ttFiber10StateAt 32 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 32 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 32) ttFiber10FirstPassGrows
    ttFiber10State32_in_pass2_full

theorem ttFiber10State33_in_close :
    ttFiber10StateAt 33 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 33 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 33) ttFiber10FirstPassGrows
    ttFiber10State33_in_pass2_full

theorem ttFiber10State34_in_close :
    ttFiber10StateAt 34 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 34 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 34) ttFiber10State34_in_pass1_full

theorem ttFiber10State35_in_close :
    ttFiber10StateAt 35 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 35 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 35) ttFiber10State35_in_pass1_full

theorem ttFiber10State36_in_close :
    ttFiber10StateAt 36 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 36 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 36) ttFiber10State36_in_pass1_full

theorem ttFiber10State37_in_close :
    ttFiber10StateAt 37 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 37 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 37) ttFiber10FirstPassGrows
    ttFiber10State37_in_pass2_full

theorem ttFiber10State38_in_close :
    ttFiber10StateAt 38 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 38 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 38) ttFiber10State38_in_pass1_full

theorem ttFiber10State39_in_close :
    ttFiber10StateAt 39 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 39 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 39) ttFiber10State39_in_pass1_full

theorem ttFiber10State40_in_close :
    ttFiber10StateAt 40 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 40 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 40) ttFiber10FirstPassGrows
    ttFiber10State40_in_pass2_full

theorem ttFiber10State41_in_close :
    ttFiber10StateAt 41 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 41 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 41) ttFiber10FirstPassGrows
    ttFiber10State41_in_pass2_full

theorem ttFiber10State42_in_close :
    ttFiber10StateAt 42 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 42 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 42) ttFiber10FirstPassGrows
    ttFiber10State42_in_pass2_full

theorem ttFiber10State43_in_close :
    ttFiber10StateAt 43 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 43 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 43) ttFiber10FirstPassGrows
    ttFiber10State43_in_pass2_full

theorem ttFiber10State44_in_close :
    ttFiber10StateAt 44 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 44 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 44) ttFiber10FirstPassGrows
    ttFiber10State44_in_pass2_full

theorem ttFiber10State45_in_close :
    ttFiber10StateAt 45 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 45 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 45) ttFiber10FirstPassGrows
    ttFiber10State45_in_pass2_full

theorem ttFiber10State46_in_close :
    ttFiber10StateAt 46 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 46 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 46) ttFiber10FirstPassGrows
    ttFiber10State46_in_pass2_full

theorem ttFiber10State47_in_close :
    ttFiber10StateAt 47 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 47 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 47) ttFiber10FirstPassGrows
    ttFiber10State47_in_pass2_full

theorem ttFiber10State48_in_close :
    ttFiber10StateAt 48 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 48 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 48) ttFiber10State48_in_pass1_full

theorem ttFiber10State49_in_close :
    ttFiber10StateAt 49 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 49 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 49) ttFiber10State49_in_pass1_full

theorem ttFiber10State50_in_close :
    ttFiber10StateAt 50 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 50 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 50) ttFiber10State50_in_pass1_full

theorem ttFiber10State51_in_close :
    ttFiber10StateAt 51 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 51 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 51) ttFiber10State51_in_pass1_full

theorem ttFiber10State52_in_close :
    ttFiber10StateAt 52 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 52 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 52) ttFiber10State52_in_pass1_full

theorem ttFiber10State53_in_close :
    ttFiber10StateAt 53 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 53 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 53) ttFiber10FirstPassGrows
    ttFiber10State53_in_pass2_full

theorem ttFiber10State54_in_close :
    ttFiber10StateAt 54 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 54 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 54) ttFiber10State54_in_pass1_full

theorem ttFiber10State55_in_close :
    ttFiber10StateAt 55 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 55 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 55) ttFiber10State55_in_pass1_full

theorem ttFiber10State56_in_close :
    ttFiber10StateAt 56 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 56 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 56) ttFiber10State56_in_pass1_full

theorem ttFiber10State57_in_close :
    ttFiber10StateAt 57 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 57 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 57) ttFiber10State57_in_pass1_full

theorem ttFiber10State58_in_close :
    ttFiber10StateAt 58 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 58 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 58) ttFiber10State58_in_pass1_full

theorem ttFiber10State59_in_close :
    ttFiber10StateAt 59 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 59 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 59) ttFiber10State59_in_pass1_full

theorem ttFiber10State60_in_close :
    ttFiber10StateAt 60 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 60 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 60) ttFiber10State60_in_pass1_full

theorem ttFiber10State61_in_close :
    ttFiber10StateAt 61 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 61 ∈ closeChainFiber ttWord ttFiber10DirectStates (62 + 2)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber10DirectStates 62
    [ttFiber10StateAt 0] (ttFiber10StateAt 61) ttFiber10FirstPassGrows
    ttFiber10State61_in_pass2_full

theorem ttFiber10State62_in_close :
    ttFiber10StateAt 62 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 62 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 62) ttFiber10State62_in_pass1_full

theorem ttFiber10State63_in_close :
    ttFiber10StateAt 63 ∈
      closeChainFiber ttWord ttFiber10DirectStates ttFiber10DirectStates.length
        [ttFiber10StateAt 0] := by
  change ttFiber10StateAt 63 ∈ closeChainFiber ttWord ttFiber10DirectStates (63 + 1)
    [ttFiber10StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber10DirectStates 63
    [ttFiber10StateAt 0] (ttFiber10StateAt 63) ttFiber10State63_in_pass1_full

theorem ttFiber10DirectConnected :
    chainFiberConnected ttWord ttFiber10DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber10DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber10State0_in_close
  · subst state
    exact ttFiber10State1_in_close
  · subst state
    exact ttFiber10State2_in_close
  · subst state
    exact ttFiber10State3_in_close
  · subst state
    exact ttFiber10State4_in_close
  · subst state
    exact ttFiber10State5_in_close
  · subst state
    exact ttFiber10State6_in_close
  · subst state
    exact ttFiber10State7_in_close
  · subst state
    exact ttFiber10State8_in_close
  · subst state
    exact ttFiber10State9_in_close
  · subst state
    exact ttFiber10State10_in_close
  · subst state
    exact ttFiber10State11_in_close
  · subst state
    exact ttFiber10State12_in_close
  · subst state
    exact ttFiber10State13_in_close
  · subst state
    exact ttFiber10State14_in_close
  · subst state
    exact ttFiber10State15_in_close
  · subst state
    exact ttFiber10State16_in_close
  · subst state
    exact ttFiber10State17_in_close
  · subst state
    exact ttFiber10State18_in_close
  · subst state
    exact ttFiber10State19_in_close
  · subst state
    exact ttFiber10State20_in_close
  · subst state
    exact ttFiber10State21_in_close
  · subst state
    exact ttFiber10State22_in_close
  · subst state
    exact ttFiber10State23_in_close
  · subst state
    exact ttFiber10State24_in_close
  · subst state
    exact ttFiber10State25_in_close
  · subst state
    exact ttFiber10State26_in_close
  · subst state
    exact ttFiber10State27_in_close
  · subst state
    exact ttFiber10State28_in_close
  · subst state
    exact ttFiber10State29_in_close
  · subst state
    exact ttFiber10State30_in_close
  · subst state
    exact ttFiber10State31_in_close
  · subst state
    exact ttFiber10State32_in_close
  · subst state
    exact ttFiber10State33_in_close
  · subst state
    exact ttFiber10State34_in_close
  · subst state
    exact ttFiber10State35_in_close
  · subst state
    exact ttFiber10State36_in_close
  · subst state
    exact ttFiber10State37_in_close
  · subst state
    exact ttFiber10State38_in_close
  · subst state
    exact ttFiber10State39_in_close
  · subst state
    exact ttFiber10State40_in_close
  · subst state
    exact ttFiber10State41_in_close
  · subst state
    exact ttFiber10State42_in_close
  · subst state
    exact ttFiber10State43_in_close
  · subst state
    exact ttFiber10State44_in_close
  · subst state
    exact ttFiber10State45_in_close
  · subst state
    exact ttFiber10State46_in_close
  · subst state
    exact ttFiber10State47_in_close
  · subst state
    exact ttFiber10State48_in_close
  · subst state
    exact ttFiber10State49_in_close
  · subst state
    exact ttFiber10State50_in_close
  · subst state
    exact ttFiber10State51_in_close
  · subst state
    exact ttFiber10State52_in_close
  · subst state
    exact ttFiber10State53_in_close
  · subst state
    exact ttFiber10State54_in_close
  · subst state
    exact ttFiber10State55_in_close
  · subst state
    exact ttFiber10State56_in_close
  · subst state
    exact ttFiber10State57_in_close
  · subst state
    exact ttFiber10State58_in_close
  · subst state
    exact ttFiber10State59_in_close
  · subst state
    exact ttFiber10State60_in_close
  · subst state
    exact ttFiber10State61_in_close
  · subst state
    exact ttFiber10State62_in_close
  · subst state
    exact ttFiber10State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
