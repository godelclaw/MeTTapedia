import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Prototype multi-pass direct closure bridge for generated length-two fiber ttFiber70

This module checks the proof shape for a generated `tau,tau` fiber whose
parent order requires two closure scans.  It remains a local bridge
prototype, not the final real `chainLKRInAudit` theorem.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber70StateAt (i : Nat) : List TauState :=
  directStates (ttFiber70RowAt i).sourceLeft (ttFiber70RowAt i).sourceRight

def ttFiber70DirectStates : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]

def ttFiber70Prefix0 : List (List TauState) :=
  [ttFiber70StateAt 0]

def ttFiber70Prefix1 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1]

def ttFiber70Prefix2 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2]

def ttFiber70Prefix3 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3]

def ttFiber70Prefix4 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4]

def ttFiber70Prefix5 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5]

def ttFiber70Prefix6 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6]

def ttFiber70Prefix7 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7]

def ttFiber70Prefix8 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8]

def ttFiber70Prefix9 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9]

def ttFiber70Prefix10 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10]

def ttFiber70Prefix11 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11]

def ttFiber70Prefix12 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12]

def ttFiber70Prefix13 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13]

def ttFiber70Prefix14 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14]

def ttFiber70Prefix15 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15]

def ttFiber70Prefix16 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16]

def ttFiber70Prefix17 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17]

def ttFiber70Prefix18 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18]

def ttFiber70Prefix19 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19]

def ttFiber70Prefix20 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20]

def ttFiber70Prefix21 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21]

def ttFiber70Prefix22 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22]

def ttFiber70Prefix23 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23]

def ttFiber70Prefix24 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24]

def ttFiber70Prefix25 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25]

def ttFiber70Prefix26 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26]

def ttFiber70Prefix27 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27]

def ttFiber70Prefix28 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28]

def ttFiber70Prefix29 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29]

def ttFiber70Prefix30 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30]

def ttFiber70Prefix31 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31]

def ttFiber70Prefix32 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32]

def ttFiber70Prefix33 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33]

def ttFiber70Prefix34 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34]

def ttFiber70Prefix35 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35]

def ttFiber70Prefix36 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36]

def ttFiber70Prefix37 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37]

def ttFiber70Prefix38 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38]

def ttFiber70Prefix39 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39]

def ttFiber70Prefix40 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40]

def ttFiber70Prefix41 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41]

def ttFiber70Prefix42 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42]

def ttFiber70Prefix43 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43]

def ttFiber70Prefix44 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44]

def ttFiber70Prefix45 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45]

def ttFiber70Prefix46 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46]

def ttFiber70Prefix47 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47]

def ttFiber70Prefix48 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48]

def ttFiber70Prefix49 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49]

def ttFiber70Prefix50 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50]

def ttFiber70Prefix51 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51]

def ttFiber70Prefix52 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52]

def ttFiber70Prefix53 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53]

def ttFiber70Prefix54 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54]

def ttFiber70Prefix55 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55]

def ttFiber70Prefix56 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56]

def ttFiber70Prefix57 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57]

def ttFiber70Prefix58 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58]

def ttFiber70Prefix59 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59]

def ttFiber70Prefix60 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60]

def ttFiber70Prefix61 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61]

def ttFiber70Prefix62 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62]

def ttFiber70Prefix63 : List (List TauState) :=
  [ttFiber70StateAt 0, ttFiber70StateAt 1, ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]

theorem ttFiber70ReverseRow_1_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk0] at h
  exact h.2

theorem ttFiber70ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 1)
      (ttFiber70RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 1) (by decide) ttFiber70ReverseRow_1_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_2_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk1] at h
  exact h.1

theorem ttFiber70ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 2)
      (ttFiber70RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 2) (by decide) ttFiber70ReverseRow_2_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_3_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk1] at h
  exact h.2

theorem ttFiber70ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 3)
      (ttFiber70RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 3) (by decide) ttFiber70ReverseRow_3_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_4_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk2] at h
  exact h.1

theorem ttFiber70ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 4)
      (ttFiber70RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 4) (by decide) ttFiber70ReverseRow_4_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_5_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk2] at h
  exact h.2

theorem ttFiber70ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 5)
      (ttFiber70RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 5) (by decide) ttFiber70ReverseRow_5_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_6_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk3] at h
  exact h.1

theorem ttFiber70ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 6)
      (ttFiber70RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 6) (by decide) ttFiber70ReverseRow_6_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_7_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk3] at h
  exact h.2

theorem ttFiber70ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 7)
      (ttFiber70RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 7) (by decide) ttFiber70ReverseRow_7_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_8_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk4] at h
  exact h.1

theorem ttFiber70ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 8)
      (ttFiber70RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 8) (by decide) ttFiber70ReverseRow_8_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_9_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk4] at h
  exact h.2

theorem ttFiber70ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 9)
      (ttFiber70RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 9) (by decide) ttFiber70ReverseRow_9_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_10_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk5] at h
  exact h.1

theorem ttFiber70ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 10)
      (ttFiber70RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 10) (by decide) ttFiber70ReverseRow_10_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_11_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk5] at h
  exact h.2

theorem ttFiber70ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 11)
      (ttFiber70RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 11) (by decide) ttFiber70ReverseRow_11_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_12_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk6] at h
  exact h.1

theorem ttFiber70ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 4) (ttFiber70StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 4) (ttFiber70StateAt 12)
      (ttFiber70RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 12) (by decide) ttFiber70ReverseRow_12_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_13_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk6] at h
  exact h.2

theorem ttFiber70ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 5) (ttFiber70StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 5) (ttFiber70StateAt 13)
      (ttFiber70RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 13) (by decide) ttFiber70ReverseRow_13_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_14_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk7] at h
  exact h.1

theorem ttFiber70ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 14)
      (ttFiber70RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 14) (by decide) ttFiber70ReverseRow_14_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_15_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk7] at h
  exact h.2

theorem ttFiber70ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 15)
      (ttFiber70RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 15) (by decide) ttFiber70ReverseRow_15_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_16_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk8] at h
  exact h.1

theorem ttFiber70ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 16)
      (ttFiber70RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 16) (by decide) ttFiber70ReverseRow_16_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_17_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk8] at h
  exact h.2

theorem ttFiber70ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 17)
      (ttFiber70RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 17) (by decide) ttFiber70ReverseRow_17_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_18_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk9] at h
  exact h.1

theorem ttFiber70ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 18)
      (ttFiber70RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 18) (by decide) ttFiber70ReverseRow_18_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_19_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk9] at h
  exact h.2

theorem ttFiber70ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 19)
      (ttFiber70RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 19) (by decide) ttFiber70ReverseRow_19_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_20_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk10] at h
  exact h.1

theorem ttFiber70ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 16) (ttFiber70StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 16) (ttFiber70StateAt 20)
      (ttFiber70RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 20) (by decide) ttFiber70ReverseRow_20_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_21_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk10] at h
  exact h.2

theorem ttFiber70ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 17) (ttFiber70StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 17) (ttFiber70StateAt 21)
      (ttFiber70RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 21) (by decide) ttFiber70ReverseRow_21_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_22_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk11] at h
  exact h.1

theorem ttFiber70ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 22)
      (ttFiber70RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 22) (by decide) ttFiber70ReverseRow_22_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_23_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk11] at h
  exact h.2

theorem ttFiber70ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 23)
      (ttFiber70RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 23) (by decide) ttFiber70ReverseRow_23_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_24_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk12] at h
  exact h.1

theorem ttFiber70ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 8) (ttFiber70StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 8) (ttFiber70StateAt 24)
      (ttFiber70RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 24) (by decide) ttFiber70ReverseRow_24_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_25_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk12] at h
  exact h.2

theorem ttFiber70ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 9) (ttFiber70StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 9) (ttFiber70StateAt 25)
      (ttFiber70RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 25) (by decide) ttFiber70ReverseRow_25_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_26_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk13] at h
  exact h.1

theorem ttFiber70ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 10) (ttFiber70StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 10) (ttFiber70StateAt 26)
      (ttFiber70RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 26) (by decide) ttFiber70ReverseRow_26_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_27_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk13] at h
  exact h.2

theorem ttFiber70ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 11) (ttFiber70StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 11) (ttFiber70StateAt 27)
      (ttFiber70RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 27) (by decide) ttFiber70ReverseRow_27_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_28_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk14] at h
  exact h.1

theorem ttFiber70ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 24) (ttFiber70StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 24) (ttFiber70StateAt 28)
      (ttFiber70RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 28) (by decide) ttFiber70ReverseRow_28_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_29_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk14] at h
  exact h.2

theorem ttFiber70ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 25) (ttFiber70StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 25) (ttFiber70StateAt 29)
      (ttFiber70RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 29) (by decide) ttFiber70ReverseRow_29_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_30_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk15] at h
  exact h.1

theorem ttFiber70ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 14) (ttFiber70StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 14) (ttFiber70StateAt 30)
      (ttFiber70RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 30) (by decide) ttFiber70ReverseRow_30_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_31_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk15] at h
  exact h.2

theorem ttFiber70ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 15) (ttFiber70StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 15) (ttFiber70StateAt 31)
      (ttFiber70RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 31) (by decide) ttFiber70ReverseRow_31_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_32_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk16] at h
  exact h.1

theorem ttFiber70ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 48) (ttFiber70StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 48) (ttFiber70StateAt 32)
      (ttFiber70RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 32) (by decide) ttFiber70ReverseRow_32_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_33_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk16] at h
  exact h.2

theorem ttFiber70ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 49) (ttFiber70StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 49) (ttFiber70StateAt 33)
      (ttFiber70RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 33) (by decide) ttFiber70ReverseRow_33_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_34_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk17] at h
  exact h.1

theorem ttFiber70ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 22) (ttFiber70StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 22) (ttFiber70StateAt 34)
      (ttFiber70RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 34) (by decide) ttFiber70ReverseRow_34_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_35_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk17] at h
  exact h.2

theorem ttFiber70ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 23) (ttFiber70StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 23) (ttFiber70StateAt 35)
      (ttFiber70RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 35) (by decide) ttFiber70ReverseRow_35_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_36_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk18] at h
  exact h.1

theorem ttFiber70ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 18) (ttFiber70StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 18) (ttFiber70StateAt 36)
      (ttFiber70RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 36) (by decide) ttFiber70ReverseRow_36_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_37_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk18] at h
  exact h.2

theorem ttFiber70ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 39) (ttFiber70StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 39) (ttFiber70StateAt 37)
      (ttFiber70RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 37) (by decide) ttFiber70ReverseRow_37_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_38_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk19] at h
  exact h.1

theorem ttFiber70ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 17) (ttFiber70StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 17) (ttFiber70StateAt 38)
      (ttFiber70RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 38) (by decide) ttFiber70ReverseRow_38_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_39_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk19] at h
  exact h.2

theorem ttFiber70ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 16) (ttFiber70StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 16) (ttFiber70StateAt 39)
      (ttFiber70RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 39) (by decide) ttFiber70ReverseRow_39_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_40_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk20] at h
  exact h.1

theorem ttFiber70ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 56) (ttFiber70StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 56) (ttFiber70StateAt 40)
      (ttFiber70RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 40) (by decide) ttFiber70ReverseRow_40_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_41_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk20] at h
  exact h.2

theorem ttFiber70ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 57) (ttFiber70StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 57) (ttFiber70StateAt 41)
      (ttFiber70RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 41) (by decide) ttFiber70ReverseRow_41_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_42_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk21] at h
  exact h.1

theorem ttFiber70ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 58) (ttFiber70StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 58) (ttFiber70StateAt 42)
      (ttFiber70RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 42) (by decide) ttFiber70ReverseRow_42_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_43_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk21] at h
  exact h.2

theorem ttFiber70ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 40) (ttFiber70StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 40) (ttFiber70StateAt 43)
      (ttFiber70RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 43) (by decide) ttFiber70ReverseRow_43_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_44_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk22] at h
  exact h.1

theorem ttFiber70ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 40) (ttFiber70StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 40) (ttFiber70StateAt 44)
      (ttFiber70RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 44) (by decide) ttFiber70ReverseRow_44_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_45_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk22] at h
  exact h.2

theorem ttFiber70ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 41) (ttFiber70StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 41) (ttFiber70StateAt 45)
      (ttFiber70RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 45) (by decide) ttFiber70ReverseRow_45_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_46_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk23] at h
  exact h.1

theorem ttFiber70ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 62) (ttFiber70StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 62) (ttFiber70StateAt 46)
      (ttFiber70RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 46) (by decide) ttFiber70ReverseRow_46_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_47_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk23] at h
  exact h.2

theorem ttFiber70ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 63) (ttFiber70StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 63) (ttFiber70StateAt 47)
      (ttFiber70RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 47) (by decide) ttFiber70ReverseRow_47_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_48_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk24] at h
  exact h.1

theorem ttFiber70ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 8) (ttFiber70StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 8) (ttFiber70StateAt 48)
      (ttFiber70RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 48) (by decide) ttFiber70ReverseRow_48_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_49_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk24] at h
  exact h.2

theorem ttFiber70ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 9) (ttFiber70StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 9) (ttFiber70StateAt 49)
      (ttFiber70RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 49) (by decide) ttFiber70ReverseRow_49_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_50_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk25] at h
  exact h.1

theorem ttFiber70ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 10) (ttFiber70StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 10) (ttFiber70StateAt 50)
      (ttFiber70RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 50) (by decide) ttFiber70ReverseRow_50_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_51_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk25] at h
  exact h.2

theorem ttFiber70ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 11) (ttFiber70StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 11) (ttFiber70StateAt 51)
      (ttFiber70RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 51) (by decide) ttFiber70ReverseRow_51_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_52_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk26] at h
  exact h.1

theorem ttFiber70ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 12) (ttFiber70StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 12) (ttFiber70StateAt 52)
      (ttFiber70RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 52) (by decide) ttFiber70ReverseRow_52_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_53_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk26] at h
  exact h.2

theorem ttFiber70ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 13) (ttFiber70StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 13) (ttFiber70StateAt 53)
      (ttFiber70RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 53) (by decide) ttFiber70ReverseRow_53_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_54_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk27] at h
  exact h.1

theorem ttFiber70ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 14) (ttFiber70StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 14) (ttFiber70StateAt 54)
      (ttFiber70RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 54) (by decide) ttFiber70ReverseRow_54_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_55_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk27] at h
  exact h.2

theorem ttFiber70ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 15) (ttFiber70StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 15) (ttFiber70StateAt 55)
      (ttFiber70RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 55) (by decide) ttFiber70ReverseRow_55_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_56_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk28] at h
  exact h.1

theorem ttFiber70ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 0) (ttFiber70StateAt 56)
      (ttFiber70RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 56) (by decide) ttFiber70ReverseRow_56_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_57_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk28] at h
  exact h.2

theorem ttFiber70ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 1) (ttFiber70StateAt 57)
      (ttFiber70RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 57) (by decide) ttFiber70ReverseRow_57_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_58_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk29] at h
  exact h.1

theorem ttFiber70ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 2) (ttFiber70StateAt 58)
      (ttFiber70RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 58) (by decide) ttFiber70ReverseRow_58_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_59_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk29] at h
  exact h.2

theorem ttFiber70ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 3) (ttFiber70StateAt 59)
      (ttFiber70RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 59) (by decide) ttFiber70ReverseRow_59_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_60_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk30] at h
  exact h.1

theorem ttFiber70ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 4) (ttFiber70StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 4) (ttFiber70StateAt 60)
      (ttFiber70RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 60) (by decide) ttFiber70ReverseRow_60_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_61_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk30] at h
  exact h.2

theorem ttFiber70ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 5) (ttFiber70StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 5) (ttFiber70StateAt 61)
      (ttFiber70RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 61) (by decide) ttFiber70ReverseRow_61_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_62_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk31] at h
  exact h.1

theorem ttFiber70ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 6) (ttFiber70StateAt 62)
      (ttFiber70RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 62) (by decide) ttFiber70ReverseRow_62_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70ReverseRow_63_ok' :
    directRowReverseValid ttFiber70Key ttFiber70Expected (ttFiber70RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber70Chunk31] at h
  exact h.2

theorem ttFiber70ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber70StateAt 7) (ttFiber70StateAt 63)
      (ttFiber70RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber70Key ttFiber70Expected
      (ttFiber70RowAt 63) (by decide) ttFiber70ReverseRow_63_ok'
    simpa [ttFiber70StateAt, ttFiber70RowAt, ttFiber70Rows, listGetD, directRow] using h

theorem ttFiber70FirstPassGrows :
    ((chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]).length ==
      [ttFiber70StateAt 0].length) = false := by
  have hroot : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber70DirectStates [ttFiber70StateAt 0]
      (ttFiber70StateAt 0) (by simp)
  have hnew : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber70DirectStates [ttFiber70StateAt 0]
      (ttFiber70StateAt 0) (ttFiber70StateAt 1) (by decide) (by simp)
      ttFiber70ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0])
    (ttFiber70StateAt 0) (ttFiber70StateAt 1) hroot hnew (by decide)

theorem ttFiber70State0_in_pass0_full :
    ttFiber70StateAt 0 ∈ [ttFiber70StateAt 0] := by
  simp

theorem ttFiber70State1_in_pass1_prefix1 :
    ttFiber70StateAt 1 ∈ chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix0 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix0
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix1 = ttFiber70Prefix0 ++ [ttFiber70StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 1) []
    (chainClosureStep ttWord ttFiber70Prefix0 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep1

theorem ttFiber70State1_in_pass1_full :
    ttFiber70StateAt 1 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix1 ++ [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1

theorem ttFiber70State2_in_pass1_prefix2 :
    ttFiber70StateAt 2 ∈ chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix1
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix2 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 2) []
    (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep2

theorem ttFiber70State2_in_pass1_full :
    ttFiber70StateAt 2 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix2 ++ [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 2) ttFiber70State2_in_pass1_prefix2

theorem ttFiber70State3_in_pass1_prefix3 :
    ttFiber70StateAt 3 ∈ chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix2 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2]
      (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1
  rw [show ttFiber70Prefix3 = ttFiber70Prefix2 ++ [ttFiber70StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 3) []
    (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) hparentBefore ttFiber70ReverseSingleStep3

theorem ttFiber70State3_in_pass1_full :
    ttFiber70StateAt 3 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix3 ++ [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 3) ttFiber70State3_in_pass1_prefix3

theorem ttFiber70State4_in_pass1_prefix4 :
    ttFiber70StateAt 4 ∈ chainClosureStep ttWord ttFiber70Prefix4 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 2 ∈
      chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix3 = ttFiber70Prefix2 ++ [ttFiber70StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 3]
      (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 2) ttFiber70State2_in_pass1_prefix2
  rw [show ttFiber70Prefix4 = ttFiber70Prefix3 ++ [ttFiber70StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 4) []
    (chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 2) hparentBefore ttFiber70ReverseSingleStep4

theorem ttFiber70State4_in_pass1_full :
    ttFiber70StateAt 4 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix4 ++ [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix4 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 4) ttFiber70State4_in_pass1_prefix4

theorem ttFiber70State6_in_pass1_prefix6 :
    ttFiber70StateAt 6 ∈ chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70Prefix5 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix5 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5]
      (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1
  rw [show ttFiber70Prefix6 = ttFiber70Prefix5 ++ [ttFiber70StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 6) []
    (chainClosureStep ttWord ttFiber70Prefix5 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) hparentBefore ttFiber70ReverseSingleStep6

theorem ttFiber70State6_in_pass1_full :
    ttFiber70StateAt 6 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix6 ++ [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 6) ttFiber70State6_in_pass1_prefix6

theorem ttFiber70State7_in_pass1_prefix7 :
    ttFiber70StateAt 7 ∈ chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix6
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix7 = ttFiber70Prefix6 ++ [ttFiber70StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 7) []
    (chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep7

theorem ttFiber70State7_in_pass1_full :
    ttFiber70StateAt 7 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix7 ++ [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 7) ttFiber70State7_in_pass1_prefix7

theorem ttFiber70State8_in_pass1_prefix8 :
    ttFiber70StateAt 8 ∈ chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix7
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix8 = ttFiber70Prefix7 ++ [ttFiber70StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 8) []
    (chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep8

theorem ttFiber70State8_in_pass1_full :
    ttFiber70StateAt 8 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix8 ++ [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 8) ttFiber70State8_in_pass1_prefix8

theorem ttFiber70State9_in_pass1_prefix9 :
    ttFiber70StateAt 9 ∈ chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix8 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8]
      (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1
  rw [show ttFiber70Prefix9 = ttFiber70Prefix8 ++ [ttFiber70StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 9) []
    (chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) hparentBefore ttFiber70ReverseSingleStep9

theorem ttFiber70State9_in_pass1_full :
    ttFiber70StateAt 9 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix9 ++ [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 9) ttFiber70State9_in_pass1_prefix9

theorem ttFiber70State10_in_pass1_prefix10 :
    ttFiber70StateAt 10 ∈ chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 2 ∈
      chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix9 = ttFiber70Prefix2 ++ [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9]
      (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 2) ttFiber70State2_in_pass1_prefix2
  rw [show ttFiber70Prefix10 = ttFiber70Prefix9 ++ [ttFiber70StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 10) []
    (chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 2) hparentBefore ttFiber70ReverseSingleStep10

theorem ttFiber70State10_in_pass1_full :
    ttFiber70StateAt 10 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix10 ++ [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 10) ttFiber70State10_in_pass1_prefix10

theorem ttFiber70State11_in_pass1_prefix11 :
    ttFiber70StateAt 11 ∈ chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 3 ∈
      chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix10 = ttFiber70Prefix3 ++ [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10]
      (chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 3) ttFiber70State3_in_pass1_prefix3
  rw [show ttFiber70Prefix11 = ttFiber70Prefix10 ++ [ttFiber70StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 11) []
    (chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 3) hparentBefore ttFiber70ReverseSingleStep11

theorem ttFiber70State11_in_pass1_full :
    ttFiber70StateAt 11 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix11 ++ [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 11) ttFiber70State11_in_pass1_prefix11

theorem ttFiber70State12_in_pass1_prefix12 :
    ttFiber70StateAt 12 ∈ chainClosureStep ttWord ttFiber70Prefix12 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 4 ∈
      chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix11 = ttFiber70Prefix4 ++ [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11]
      (chainClosureStep ttWord ttFiber70Prefix4 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 4) ttFiber70State4_in_pass1_prefix4
  rw [show ttFiber70Prefix12 = ttFiber70Prefix11 ++ [ttFiber70StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 12) []
    (chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 4) hparentBefore ttFiber70ReverseSingleStep12

theorem ttFiber70State12_in_pass1_full :
    ttFiber70StateAt 12 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix12 ++ [ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix12 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 12) ttFiber70State12_in_pass1_prefix12

theorem ttFiber70State14_in_pass1_prefix14 :
    ttFiber70StateAt 14 ∈ chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 6 ∈
      chainClosureStep ttWord ttFiber70Prefix13 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix13 = ttFiber70Prefix6 ++ [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13]
      (chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 6) ttFiber70State6_in_pass1_prefix6
  rw [show ttFiber70Prefix14 = ttFiber70Prefix13 ++ [ttFiber70StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 14) []
    (chainClosureStep ttWord ttFiber70Prefix13 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 6) hparentBefore ttFiber70ReverseSingleStep14

theorem ttFiber70State14_in_pass1_full :
    ttFiber70StateAt 14 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix14 ++ [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 14) ttFiber70State14_in_pass1_prefix14

theorem ttFiber70State15_in_pass1_prefix15 :
    ttFiber70StateAt 15 ∈ chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 7 ∈
      chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix14 = ttFiber70Prefix7 ++ [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14]
      (chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 7) ttFiber70State7_in_pass1_prefix7
  rw [show ttFiber70Prefix15 = ttFiber70Prefix14 ++ [ttFiber70StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 15) []
    (chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 7) hparentBefore ttFiber70ReverseSingleStep15

theorem ttFiber70State15_in_pass1_full :
    ttFiber70StateAt 15 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix15 ++ [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 15) ttFiber70State15_in_pass1_prefix15

theorem ttFiber70State16_in_pass1_prefix16 :
    ttFiber70StateAt 16 ∈ chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix15
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix16 = ttFiber70Prefix15 ++ [ttFiber70StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 16) []
    (chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep16

theorem ttFiber70State16_in_pass1_full :
    ttFiber70StateAt 16 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix16 ++ [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 16) ttFiber70State16_in_pass1_prefix16

theorem ttFiber70State17_in_pass1_prefix17 :
    ttFiber70StateAt 17 ∈ chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix16 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16]
      (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1
  rw [show ttFiber70Prefix17 = ttFiber70Prefix16 ++ [ttFiber70StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 17) []
    (chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) hparentBefore ttFiber70ReverseSingleStep17

theorem ttFiber70State17_in_pass1_full :
    ttFiber70StateAt 17 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix17 ++ [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 17) ttFiber70State17_in_pass1_prefix17

theorem ttFiber70State18_in_pass1_prefix18 :
    ttFiber70StateAt 18 ∈ chainClosureStep ttWord ttFiber70Prefix18 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 2 ∈
      chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix17 = ttFiber70Prefix2 ++ [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17]
      (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 2) ttFiber70State2_in_pass1_prefix2
  rw [show ttFiber70Prefix18 = ttFiber70Prefix17 ++ [ttFiber70StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 18) []
    (chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 2) hparentBefore ttFiber70ReverseSingleStep18

theorem ttFiber70State18_in_pass1_full :
    ttFiber70StateAt 18 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix18 ++ [ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix18 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 18) ttFiber70State18_in_pass1_prefix18

theorem ttFiber70State19_in_pass1_prefix19 :
    ttFiber70StateAt 19 ∈ chainClosureStep ttWord ttFiber70Prefix19 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 3 ∈
      chainClosureStep ttWord ttFiber70Prefix18 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix18 = ttFiber70Prefix3 ++ [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18]
      (chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 3) ttFiber70State3_in_pass1_prefix3
  rw [show ttFiber70Prefix19 = ttFiber70Prefix18 ++ [ttFiber70StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 19) []
    (chainClosureStep ttWord ttFiber70Prefix18 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 3) hparentBefore ttFiber70ReverseSingleStep19

theorem ttFiber70State19_in_pass1_full :
    ttFiber70StateAt 19 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix19 ++ [ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix19 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 19) ttFiber70State19_in_pass1_prefix19

theorem ttFiber70State20_in_pass1_prefix20 :
    ttFiber70StateAt 20 ∈ chainClosureStep ttWord ttFiber70Prefix20 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 16 ∈
      chainClosureStep ttWord ttFiber70Prefix19 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix19 = ttFiber70Prefix16 ++ [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19]
      (chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 16) ttFiber70State16_in_pass1_prefix16
  rw [show ttFiber70Prefix20 = ttFiber70Prefix19 ++ [ttFiber70StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 20) []
    (chainClosureStep ttWord ttFiber70Prefix19 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 16) hparentBefore ttFiber70ReverseSingleStep20

theorem ttFiber70State20_in_pass1_full :
    ttFiber70StateAt 20 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix20 ++ [ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix20 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 20) ttFiber70State20_in_pass1_prefix20

theorem ttFiber70State21_in_pass1_prefix21 :
    ttFiber70StateAt 21 ∈ chainClosureStep ttWord ttFiber70Prefix21 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 17 ∈
      chainClosureStep ttWord ttFiber70Prefix20 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix20 = ttFiber70Prefix17 ++ [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20]
      (chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 17) ttFiber70State17_in_pass1_prefix17
  rw [show ttFiber70Prefix21 = ttFiber70Prefix20 ++ [ttFiber70StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 21) []
    (chainClosureStep ttWord ttFiber70Prefix20 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 17) hparentBefore ttFiber70ReverseSingleStep21

theorem ttFiber70State21_in_pass1_full :
    ttFiber70StateAt 21 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix21 ++ [ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix21 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 21) ttFiber70State21_in_pass1_prefix21

theorem ttFiber70State22_in_pass1_prefix22 :
    ttFiber70StateAt 22 ∈ chainClosureStep ttWord ttFiber70Prefix22 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 6 ∈
      chainClosureStep ttWord ttFiber70Prefix21 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix21 = ttFiber70Prefix6 ++ [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21]
      (chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 6) ttFiber70State6_in_pass1_prefix6
  rw [show ttFiber70Prefix22 = ttFiber70Prefix21 ++ [ttFiber70StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 22) []
    (chainClosureStep ttWord ttFiber70Prefix21 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 6) hparentBefore ttFiber70ReverseSingleStep22

theorem ttFiber70State22_in_pass1_full :
    ttFiber70StateAt 22 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix22 ++ [ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix22 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 22) ttFiber70State22_in_pass1_prefix22

theorem ttFiber70State23_in_pass1_prefix23 :
    ttFiber70StateAt 23 ∈ chainClosureStep ttWord ttFiber70Prefix23 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 7 ∈
      chainClosureStep ttWord ttFiber70Prefix22 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix22 = ttFiber70Prefix7 ++ [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22]
      (chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 7) ttFiber70State7_in_pass1_prefix7
  rw [show ttFiber70Prefix23 = ttFiber70Prefix22 ++ [ttFiber70StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 23) []
    (chainClosureStep ttWord ttFiber70Prefix22 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 7) hparentBefore ttFiber70ReverseSingleStep23

theorem ttFiber70State23_in_pass1_full :
    ttFiber70StateAt 23 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix23 ++ [ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix23 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 23) ttFiber70State23_in_pass1_prefix23

theorem ttFiber70State24_in_pass1_prefix24 :
    ttFiber70StateAt 24 ∈ chainClosureStep ttWord ttFiber70Prefix24 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 8 ∈
      chainClosureStep ttWord ttFiber70Prefix23 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix23 = ttFiber70Prefix8 ++ [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23]
      (chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 8) ttFiber70State8_in_pass1_prefix8
  rw [show ttFiber70Prefix24 = ttFiber70Prefix23 ++ [ttFiber70StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 24) []
    (chainClosureStep ttWord ttFiber70Prefix23 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 8) hparentBefore ttFiber70ReverseSingleStep24

theorem ttFiber70State24_in_pass1_full :
    ttFiber70StateAt 24 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix24 ++ [ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix24 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 24) ttFiber70State24_in_pass1_prefix24

theorem ttFiber70State25_in_pass1_prefix25 :
    ttFiber70StateAt 25 ∈ chainClosureStep ttWord ttFiber70Prefix25 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 9 ∈
      chainClosureStep ttWord ttFiber70Prefix24 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix24 = ttFiber70Prefix9 ++ [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24]
      (chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 9) ttFiber70State9_in_pass1_prefix9
  rw [show ttFiber70Prefix25 = ttFiber70Prefix24 ++ [ttFiber70StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 25) []
    (chainClosureStep ttWord ttFiber70Prefix24 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 9) hparentBefore ttFiber70ReverseSingleStep25

theorem ttFiber70State25_in_pass1_full :
    ttFiber70StateAt 25 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix25 ++ [ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix25 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 25) ttFiber70State25_in_pass1_prefix25

theorem ttFiber70State26_in_pass1_prefix26 :
    ttFiber70StateAt 26 ∈ chainClosureStep ttWord ttFiber70Prefix26 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 10 ∈
      chainClosureStep ttWord ttFiber70Prefix25 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix25 = ttFiber70Prefix10 ++ [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25]
      (chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 10) ttFiber70State10_in_pass1_prefix10
  rw [show ttFiber70Prefix26 = ttFiber70Prefix25 ++ [ttFiber70StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 26) []
    (chainClosureStep ttWord ttFiber70Prefix25 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 10) hparentBefore ttFiber70ReverseSingleStep26

theorem ttFiber70State26_in_pass1_full :
    ttFiber70StateAt 26 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix26 ++ [ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix26 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 26) ttFiber70State26_in_pass1_prefix26

theorem ttFiber70State27_in_pass1_prefix27 :
    ttFiber70StateAt 27 ∈ chainClosureStep ttWord ttFiber70Prefix27 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 11 ∈
      chainClosureStep ttWord ttFiber70Prefix26 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix26 = ttFiber70Prefix11 ++ [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26]
      (chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 11) ttFiber70State11_in_pass1_prefix11
  rw [show ttFiber70Prefix27 = ttFiber70Prefix26 ++ [ttFiber70StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 27) []
    (chainClosureStep ttWord ttFiber70Prefix26 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 11) hparentBefore ttFiber70ReverseSingleStep27

theorem ttFiber70State27_in_pass1_full :
    ttFiber70StateAt 27 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix27 ++ [ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix27 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 27) ttFiber70State27_in_pass1_prefix27

theorem ttFiber70State28_in_pass1_prefix28 :
    ttFiber70StateAt 28 ∈ chainClosureStep ttWord ttFiber70Prefix28 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 24 ∈
      chainClosureStep ttWord ttFiber70Prefix27 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix27 = ttFiber70Prefix24 ++ [ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27]
      (chainClosureStep ttWord ttFiber70Prefix24 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 24) ttFiber70State24_in_pass1_prefix24
  rw [show ttFiber70Prefix28 = ttFiber70Prefix27 ++ [ttFiber70StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 28) []
    (chainClosureStep ttWord ttFiber70Prefix27 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 24) hparentBefore ttFiber70ReverseSingleStep28

theorem ttFiber70State28_in_pass1_full :
    ttFiber70StateAt 28 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix28 ++ [ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix28 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 28) ttFiber70State28_in_pass1_prefix28

theorem ttFiber70State29_in_pass1_prefix29 :
    ttFiber70StateAt 29 ∈ chainClosureStep ttWord ttFiber70Prefix29 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 25 ∈
      chainClosureStep ttWord ttFiber70Prefix28 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix28 = ttFiber70Prefix25 ++ [ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28]
      (chainClosureStep ttWord ttFiber70Prefix25 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 25) ttFiber70State25_in_pass1_prefix25
  rw [show ttFiber70Prefix29 = ttFiber70Prefix28 ++ [ttFiber70StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 29) []
    (chainClosureStep ttWord ttFiber70Prefix28 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 25) hparentBefore ttFiber70ReverseSingleStep29

theorem ttFiber70State29_in_pass1_full :
    ttFiber70StateAt 29 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix29 ++ [ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix29 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 29) ttFiber70State29_in_pass1_prefix29

theorem ttFiber70State30_in_pass1_prefix30 :
    ttFiber70StateAt 30 ∈ chainClosureStep ttWord ttFiber70Prefix30 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 14 ∈
      chainClosureStep ttWord ttFiber70Prefix29 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix29 = ttFiber70Prefix14 ++ [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29]
      (chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 14) ttFiber70State14_in_pass1_prefix14
  rw [show ttFiber70Prefix30 = ttFiber70Prefix29 ++ [ttFiber70StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 30) []
    (chainClosureStep ttWord ttFiber70Prefix29 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 14) hparentBefore ttFiber70ReverseSingleStep30

theorem ttFiber70State30_in_pass1_full :
    ttFiber70StateAt 30 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix30 ++ [ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix30 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 30) ttFiber70State30_in_pass1_prefix30

theorem ttFiber70State31_in_pass1_prefix31 :
    ttFiber70StateAt 31 ∈ chainClosureStep ttWord ttFiber70Prefix31 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 15 ∈
      chainClosureStep ttWord ttFiber70Prefix30 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix30 = ttFiber70Prefix15 ++ [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30]
      (chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 15) ttFiber70State15_in_pass1_prefix15
  rw [show ttFiber70Prefix31 = ttFiber70Prefix30 ++ [ttFiber70StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 31) []
    (chainClosureStep ttWord ttFiber70Prefix30 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 15) hparentBefore ttFiber70ReverseSingleStep31

theorem ttFiber70State31_in_pass1_full :
    ttFiber70StateAt 31 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix31 ++ [ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix31 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 31) ttFiber70State31_in_pass1_prefix31

theorem ttFiber70State34_in_pass1_prefix34 :
    ttFiber70StateAt 34 ∈ chainClosureStep ttWord ttFiber70Prefix34 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 22 ∈
      chainClosureStep ttWord ttFiber70Prefix33 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix33 = ttFiber70Prefix22 ++ [ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33]
      (chainClosureStep ttWord ttFiber70Prefix22 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 22) ttFiber70State22_in_pass1_prefix22
  rw [show ttFiber70Prefix34 = ttFiber70Prefix33 ++ [ttFiber70StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 34) []
    (chainClosureStep ttWord ttFiber70Prefix33 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 22) hparentBefore ttFiber70ReverseSingleStep34

theorem ttFiber70State34_in_pass1_full :
    ttFiber70StateAt 34 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix34 ++ [ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix34 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 34) ttFiber70State34_in_pass1_prefix34

theorem ttFiber70State35_in_pass1_prefix35 :
    ttFiber70StateAt 35 ∈ chainClosureStep ttWord ttFiber70Prefix35 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 23 ∈
      chainClosureStep ttWord ttFiber70Prefix34 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix34 = ttFiber70Prefix23 ++ [ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34]
      (chainClosureStep ttWord ttFiber70Prefix23 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 23) ttFiber70State23_in_pass1_prefix23
  rw [show ttFiber70Prefix35 = ttFiber70Prefix34 ++ [ttFiber70StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 35) []
    (chainClosureStep ttWord ttFiber70Prefix34 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 23) hparentBefore ttFiber70ReverseSingleStep35

theorem ttFiber70State35_in_pass1_full :
    ttFiber70StateAt 35 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix35 ++ [ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix35 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 35) ttFiber70State35_in_pass1_prefix35

theorem ttFiber70State36_in_pass1_prefix36 :
    ttFiber70StateAt 36 ∈ chainClosureStep ttWord ttFiber70Prefix36 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 18 ∈
      chainClosureStep ttWord ttFiber70Prefix35 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix35 = ttFiber70Prefix18 ++ [ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35]
      (chainClosureStep ttWord ttFiber70Prefix18 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 18) ttFiber70State18_in_pass1_prefix18
  rw [show ttFiber70Prefix36 = ttFiber70Prefix35 ++ [ttFiber70StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 36) []
    (chainClosureStep ttWord ttFiber70Prefix35 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 18) hparentBefore ttFiber70ReverseSingleStep36

theorem ttFiber70State36_in_pass1_full :
    ttFiber70StateAt 36 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix36 ++ [ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix36 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 36) ttFiber70State36_in_pass1_prefix36

theorem ttFiber70State38_in_pass1_prefix38 :
    ttFiber70StateAt 38 ∈ chainClosureStep ttWord ttFiber70Prefix38 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 17 ∈
      chainClosureStep ttWord ttFiber70Prefix37 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix37 = ttFiber70Prefix17 ++ [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37]
      (chainClosureStep ttWord ttFiber70Prefix17 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 17) ttFiber70State17_in_pass1_prefix17
  rw [show ttFiber70Prefix38 = ttFiber70Prefix37 ++ [ttFiber70StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 38) []
    (chainClosureStep ttWord ttFiber70Prefix37 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 17) hparentBefore ttFiber70ReverseSingleStep38

theorem ttFiber70State38_in_pass1_full :
    ttFiber70StateAt 38 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix38 ++ [ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix38 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 38) ttFiber70State38_in_pass1_prefix38

theorem ttFiber70State39_in_pass1_prefix39 :
    ttFiber70StateAt 39 ∈ chainClosureStep ttWord ttFiber70Prefix39 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 16 ∈
      chainClosureStep ttWord ttFiber70Prefix38 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix38 = ttFiber70Prefix16 ++ [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38]
      (chainClosureStep ttWord ttFiber70Prefix16 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 16) ttFiber70State16_in_pass1_prefix16
  rw [show ttFiber70Prefix39 = ttFiber70Prefix38 ++ [ttFiber70StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 39) []
    (chainClosureStep ttWord ttFiber70Prefix38 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 16) hparentBefore ttFiber70ReverseSingleStep39

theorem ttFiber70State39_in_pass1_full :
    ttFiber70StateAt 39 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix39 ++ [ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix39 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 39) ttFiber70State39_in_pass1_prefix39

theorem ttFiber70State48_in_pass1_prefix48 :
    ttFiber70StateAt 48 ∈ chainClosureStep ttWord ttFiber70Prefix48 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 8 ∈
      chainClosureStep ttWord ttFiber70Prefix47 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix47 = ttFiber70Prefix8 ++ [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47]
      (chainClosureStep ttWord ttFiber70Prefix8 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 8) ttFiber70State8_in_pass1_prefix8
  rw [show ttFiber70Prefix48 = ttFiber70Prefix47 ++ [ttFiber70StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 48) []
    (chainClosureStep ttWord ttFiber70Prefix47 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 8) hparentBefore ttFiber70ReverseSingleStep48

theorem ttFiber70State48_in_pass1_full :
    ttFiber70StateAt 48 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix48 ++ [ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix48 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 48) ttFiber70State48_in_pass1_prefix48

theorem ttFiber70State49_in_pass1_prefix49 :
    ttFiber70StateAt 49 ∈ chainClosureStep ttWord ttFiber70Prefix49 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 9 ∈
      chainClosureStep ttWord ttFiber70Prefix48 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix48 = ttFiber70Prefix9 ++ [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48]
      (chainClosureStep ttWord ttFiber70Prefix9 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 9) ttFiber70State9_in_pass1_prefix9
  rw [show ttFiber70Prefix49 = ttFiber70Prefix48 ++ [ttFiber70StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 49) []
    (chainClosureStep ttWord ttFiber70Prefix48 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 9) hparentBefore ttFiber70ReverseSingleStep49

theorem ttFiber70State49_in_pass1_full :
    ttFiber70StateAt 49 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix49 ++ [ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix49 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 49) ttFiber70State49_in_pass1_prefix49

theorem ttFiber70State50_in_pass1_prefix50 :
    ttFiber70StateAt 50 ∈ chainClosureStep ttWord ttFiber70Prefix50 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 10 ∈
      chainClosureStep ttWord ttFiber70Prefix49 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix49 = ttFiber70Prefix10 ++ [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49]
      (chainClosureStep ttWord ttFiber70Prefix10 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 10) ttFiber70State10_in_pass1_prefix10
  rw [show ttFiber70Prefix50 = ttFiber70Prefix49 ++ [ttFiber70StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 50) []
    (chainClosureStep ttWord ttFiber70Prefix49 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 10) hparentBefore ttFiber70ReverseSingleStep50

theorem ttFiber70State50_in_pass1_full :
    ttFiber70StateAt 50 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix50 ++ [ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix50 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 50) ttFiber70State50_in_pass1_prefix50

theorem ttFiber70State51_in_pass1_prefix51 :
    ttFiber70StateAt 51 ∈ chainClosureStep ttWord ttFiber70Prefix51 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 11 ∈
      chainClosureStep ttWord ttFiber70Prefix50 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix50 = ttFiber70Prefix11 ++ [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50]
      (chainClosureStep ttWord ttFiber70Prefix11 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 11) ttFiber70State11_in_pass1_prefix11
  rw [show ttFiber70Prefix51 = ttFiber70Prefix50 ++ [ttFiber70StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 51) []
    (chainClosureStep ttWord ttFiber70Prefix50 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 11) hparentBefore ttFiber70ReverseSingleStep51

theorem ttFiber70State51_in_pass1_full :
    ttFiber70StateAt 51 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix51 ++ [ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix51 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 51) ttFiber70State51_in_pass1_prefix51

theorem ttFiber70State52_in_pass1_prefix52 :
    ttFiber70StateAt 52 ∈ chainClosureStep ttWord ttFiber70Prefix52 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 12 ∈
      chainClosureStep ttWord ttFiber70Prefix51 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix51 = ttFiber70Prefix12 ++ [ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51]
      (chainClosureStep ttWord ttFiber70Prefix12 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 12) ttFiber70State12_in_pass1_prefix12
  rw [show ttFiber70Prefix52 = ttFiber70Prefix51 ++ [ttFiber70StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 52) []
    (chainClosureStep ttWord ttFiber70Prefix51 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 12) hparentBefore ttFiber70ReverseSingleStep52

theorem ttFiber70State52_in_pass1_full :
    ttFiber70StateAt 52 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix52 ++ [ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix52 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 52) ttFiber70State52_in_pass1_prefix52

theorem ttFiber70State54_in_pass1_prefix54 :
    ttFiber70StateAt 54 ∈ chainClosureStep ttWord ttFiber70Prefix54 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 14 ∈
      chainClosureStep ttWord ttFiber70Prefix53 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix53 = ttFiber70Prefix14 ++ [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53]
      (chainClosureStep ttWord ttFiber70Prefix14 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 14) ttFiber70State14_in_pass1_prefix14
  rw [show ttFiber70Prefix54 = ttFiber70Prefix53 ++ [ttFiber70StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 54) []
    (chainClosureStep ttWord ttFiber70Prefix53 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 14) hparentBefore ttFiber70ReverseSingleStep54

theorem ttFiber70State54_in_pass1_full :
    ttFiber70StateAt 54 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix54 ++ [ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix54 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 54) ttFiber70State54_in_pass1_prefix54

theorem ttFiber70State55_in_pass1_prefix55 :
    ttFiber70StateAt 55 ∈ chainClosureStep ttWord ttFiber70Prefix55 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 15 ∈
      chainClosureStep ttWord ttFiber70Prefix54 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix54 = ttFiber70Prefix15 ++ [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54]
      (chainClosureStep ttWord ttFiber70Prefix15 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 15) ttFiber70State15_in_pass1_prefix15
  rw [show ttFiber70Prefix55 = ttFiber70Prefix54 ++ [ttFiber70StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 55) []
    (chainClosureStep ttWord ttFiber70Prefix54 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 15) hparentBefore ttFiber70ReverseSingleStep55

theorem ttFiber70State55_in_pass1_full :
    ttFiber70StateAt 55 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix55 ++ [ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix55 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 55) ttFiber70State55_in_pass1_prefix55

theorem ttFiber70State56_in_pass1_prefix56 :
    ttFiber70StateAt 56 ∈ chainClosureStep ttWord ttFiber70Prefix56 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 0 ∈
      chainClosureStep ttWord ttFiber70Prefix55 ([ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix55
      ([ttFiber70StateAt 0]) (ttFiber70StateAt 0) ttFiber70State0_in_pass0_full
  rw [show ttFiber70Prefix56 = ttFiber70Prefix55 ++ [ttFiber70StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 56) []
    (chainClosureStep ttWord ttFiber70Prefix55 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 0) hparentBefore ttFiber70ReverseSingleStep56

theorem ttFiber70State56_in_pass1_full :
    ttFiber70StateAt 56 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix56 ++ [ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix56 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 56) ttFiber70State56_in_pass1_prefix56

theorem ttFiber70State57_in_pass1_prefix57 :
    ttFiber70StateAt 57 ∈ chainClosureStep ttWord ttFiber70Prefix57 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 1 ∈
      chainClosureStep ttWord ttFiber70Prefix56 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix56 = ttFiber70Prefix1 ++ [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 2, ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56]
      (chainClosureStep ttWord ttFiber70Prefix1 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 1) ttFiber70State1_in_pass1_prefix1
  rw [show ttFiber70Prefix57 = ttFiber70Prefix56 ++ [ttFiber70StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 57) []
    (chainClosureStep ttWord ttFiber70Prefix56 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 1) hparentBefore ttFiber70ReverseSingleStep57

theorem ttFiber70State57_in_pass1_full :
    ttFiber70StateAt 57 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix57 ++ [ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix57 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 57) ttFiber70State57_in_pass1_prefix57

theorem ttFiber70State58_in_pass1_prefix58 :
    ttFiber70StateAt 58 ∈ chainClosureStep ttWord ttFiber70Prefix58 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 2 ∈
      chainClosureStep ttWord ttFiber70Prefix57 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix57 = ttFiber70Prefix2 ++ [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 3, ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57]
      (chainClosureStep ttWord ttFiber70Prefix2 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 2) ttFiber70State2_in_pass1_prefix2
  rw [show ttFiber70Prefix58 = ttFiber70Prefix57 ++ [ttFiber70StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 58) []
    (chainClosureStep ttWord ttFiber70Prefix57 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 2) hparentBefore ttFiber70ReverseSingleStep58

theorem ttFiber70State58_in_pass1_full :
    ttFiber70StateAt 58 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix58 ++ [ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix58 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 58) ttFiber70State58_in_pass1_prefix58

theorem ttFiber70State59_in_pass1_prefix59 :
    ttFiber70StateAt 59 ∈ chainClosureStep ttWord ttFiber70Prefix59 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 3 ∈
      chainClosureStep ttWord ttFiber70Prefix58 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix58 = ttFiber70Prefix3 ++ [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 4, ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58]
      (chainClosureStep ttWord ttFiber70Prefix3 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 3) ttFiber70State3_in_pass1_prefix3
  rw [show ttFiber70Prefix59 = ttFiber70Prefix58 ++ [ttFiber70StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 59) []
    (chainClosureStep ttWord ttFiber70Prefix58 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 3) hparentBefore ttFiber70ReverseSingleStep59

theorem ttFiber70State59_in_pass1_full :
    ttFiber70StateAt 59 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix59 ++ [ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix59 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 59) ttFiber70State59_in_pass1_prefix59

theorem ttFiber70State60_in_pass1_prefix60 :
    ttFiber70StateAt 60 ∈ chainClosureStep ttWord ttFiber70Prefix60 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 4 ∈
      chainClosureStep ttWord ttFiber70Prefix59 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix59 = ttFiber70Prefix4 ++ [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 5, ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59]
      (chainClosureStep ttWord ttFiber70Prefix4 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 4) ttFiber70State4_in_pass1_prefix4
  rw [show ttFiber70Prefix60 = ttFiber70Prefix59 ++ [ttFiber70StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 60) []
    (chainClosureStep ttWord ttFiber70Prefix59 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 4) hparentBefore ttFiber70ReverseSingleStep60

theorem ttFiber70State60_in_pass1_full :
    ttFiber70StateAt 60 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix60 ++ [ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix60 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 60) ttFiber70State60_in_pass1_prefix60

theorem ttFiber70State62_in_pass1_prefix62 :
    ttFiber70StateAt 62 ∈ chainClosureStep ttWord ttFiber70Prefix62 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 6 ∈
      chainClosureStep ttWord ttFiber70Prefix61 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix61 = ttFiber70Prefix6 ++ [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61]
      (chainClosureStep ttWord ttFiber70Prefix6 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 6) ttFiber70State6_in_pass1_prefix6
  rw [show ttFiber70Prefix62 = ttFiber70Prefix61 ++ [ttFiber70StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 62) []
    (chainClosureStep ttWord ttFiber70Prefix61 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 6) hparentBefore ttFiber70ReverseSingleStep62

theorem ttFiber70State62_in_pass1_full :
    ttFiber70StateAt 62 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix62 ++ [ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix62 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 62) ttFiber70State62_in_pass1_prefix62

theorem ttFiber70State63_in_pass1_prefix63 :
    ttFiber70StateAt 63 ∈ chainClosureStep ttWord ttFiber70Prefix63 ([ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 7 ∈
      chainClosureStep ttWord ttFiber70Prefix62 ([ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix62 = ttFiber70Prefix7 ++ [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62]
      (chainClosureStep ttWord ttFiber70Prefix7 ([ttFiber70StateAt 0]))
      (ttFiber70StateAt 7) ttFiber70State7_in_pass1_prefix7
  rw [show ttFiber70Prefix63 = ttFiber70Prefix62 ++ [ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 63) []
    (chainClosureStep ttWord ttFiber70Prefix62 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 7) hparentBefore ttFiber70ReverseSingleStep63

theorem ttFiber70State63_in_pass1_full :
    ttFiber70StateAt 63 ∈ chainClosureStep ttWord ttFiber70DirectStates ([ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber70Prefix63 ([ttFiber70StateAt 0]))
    (ttFiber70StateAt 63) ttFiber70State63_in_pass1_prefix63

theorem ttFiber70State5_in_pass2_prefix5 :
    ttFiber70StateAt 5 ∈ chainClosureStep ttWord ttFiber70Prefix5 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 7 ∈
      chainClosureStep ttWord ttFiber70Prefix4 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix4
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 7) ttFiber70State7_in_pass1_full
  rw [show ttFiber70Prefix5 = ttFiber70Prefix4 ++ [ttFiber70StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 5) []
    (chainClosureStep ttWord ttFiber70Prefix4 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 7) hparentBefore ttFiber70ReverseSingleStep5

theorem ttFiber70State5_in_pass2_full :
    ttFiber70StateAt 5 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix5 ++ [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix5 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 5) ttFiber70State5_in_pass2_prefix5

theorem ttFiber70State13_in_pass2_prefix13 :
    ttFiber70StateAt 13 ∈ chainClosureStep ttWord ttFiber70Prefix13 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 5 ∈
      chainClosureStep ttWord ttFiber70Prefix12 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix12 = ttFiber70Prefix5 ++ [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12]
      (chainClosureStep ttWord ttFiber70Prefix5 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 5) ttFiber70State5_in_pass2_prefix5
  rw [show ttFiber70Prefix13 = ttFiber70Prefix12 ++ [ttFiber70StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 13) []
    (chainClosureStep ttWord ttFiber70Prefix12 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 5) hparentBefore ttFiber70ReverseSingleStep13

theorem ttFiber70State13_in_pass2_full :
    ttFiber70StateAt 13 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix13 ++ [ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix13 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 13) ttFiber70State13_in_pass2_prefix13

theorem ttFiber70State32_in_pass2_prefix32 :
    ttFiber70StateAt 32 ∈ chainClosureStep ttWord ttFiber70Prefix32 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 48 ∈
      chainClosureStep ttWord ttFiber70Prefix31 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix31
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 48) ttFiber70State48_in_pass1_full
  rw [show ttFiber70Prefix32 = ttFiber70Prefix31 ++ [ttFiber70StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 32) []
    (chainClosureStep ttWord ttFiber70Prefix31 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 48) hparentBefore ttFiber70ReverseSingleStep32

theorem ttFiber70State32_in_pass2_full :
    ttFiber70StateAt 32 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix32 ++ [ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix32 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 32) ttFiber70State32_in_pass2_prefix32

theorem ttFiber70State33_in_pass2_prefix33 :
    ttFiber70StateAt 33 ∈ chainClosureStep ttWord ttFiber70Prefix33 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 49 ∈
      chainClosureStep ttWord ttFiber70Prefix32 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix32
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 49) ttFiber70State49_in_pass1_full
  rw [show ttFiber70Prefix33 = ttFiber70Prefix32 ++ [ttFiber70StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 33) []
    (chainClosureStep ttWord ttFiber70Prefix32 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 49) hparentBefore ttFiber70ReverseSingleStep33

theorem ttFiber70State33_in_pass2_full :
    ttFiber70StateAt 33 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix33 ++ [ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix33 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 33) ttFiber70State33_in_pass2_prefix33

theorem ttFiber70State37_in_pass2_prefix37 :
    ttFiber70StateAt 37 ∈ chainClosureStep ttWord ttFiber70Prefix37 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 39 ∈
      chainClosureStep ttWord ttFiber70Prefix36 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix36
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 39) ttFiber70State39_in_pass1_full
  rw [show ttFiber70Prefix37 = ttFiber70Prefix36 ++ [ttFiber70StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 37) []
    (chainClosureStep ttWord ttFiber70Prefix36 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 39) hparentBefore ttFiber70ReverseSingleStep37

theorem ttFiber70State37_in_pass2_full :
    ttFiber70StateAt 37 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix37 ++ [ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix37 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 37) ttFiber70State37_in_pass2_prefix37

theorem ttFiber70State40_in_pass2_prefix40 :
    ttFiber70StateAt 40 ∈ chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 56 ∈
      chainClosureStep ttWord ttFiber70Prefix39 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix39
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 56) ttFiber70State56_in_pass1_full
  rw [show ttFiber70Prefix40 = ttFiber70Prefix39 ++ [ttFiber70StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 40) []
    (chainClosureStep ttWord ttFiber70Prefix39 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 56) hparentBefore ttFiber70ReverseSingleStep40

theorem ttFiber70State40_in_pass2_full :
    ttFiber70StateAt 40 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix40 ++ [ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 40) ttFiber70State40_in_pass2_prefix40

theorem ttFiber70State41_in_pass2_prefix41 :
    ttFiber70StateAt 41 ∈ chainClosureStep ttWord ttFiber70Prefix41 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 57 ∈
      chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix40
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 57) ttFiber70State57_in_pass1_full
  rw [show ttFiber70Prefix41 = ttFiber70Prefix40 ++ [ttFiber70StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 41) []
    (chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 57) hparentBefore ttFiber70ReverseSingleStep41

theorem ttFiber70State41_in_pass2_full :
    ttFiber70StateAt 41 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix41 ++ [ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix41 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 41) ttFiber70State41_in_pass2_prefix41

theorem ttFiber70State42_in_pass2_prefix42 :
    ttFiber70StateAt 42 ∈ chainClosureStep ttWord ttFiber70Prefix42 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 58 ∈
      chainClosureStep ttWord ttFiber70Prefix41 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix41
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 58) ttFiber70State58_in_pass1_full
  rw [show ttFiber70Prefix42 = ttFiber70Prefix41 ++ [ttFiber70StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 42) []
    (chainClosureStep ttWord ttFiber70Prefix41 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 58) hparentBefore ttFiber70ReverseSingleStep42

theorem ttFiber70State42_in_pass2_full :
    ttFiber70StateAt 42 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix42 ++ [ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix42 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 42) ttFiber70State42_in_pass2_prefix42

theorem ttFiber70State43_in_pass2_prefix43 :
    ttFiber70StateAt 43 ∈ chainClosureStep ttWord ttFiber70Prefix43 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 40 ∈
      chainClosureStep ttWord ttFiber70Prefix42 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix42 = ttFiber70Prefix40 ++ [ttFiber70StateAt 41, ttFiber70StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 41, ttFiber70StateAt 42]
      (chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 40) ttFiber70State40_in_pass2_prefix40
  rw [show ttFiber70Prefix43 = ttFiber70Prefix42 ++ [ttFiber70StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 43) []
    (chainClosureStep ttWord ttFiber70Prefix42 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 40) hparentBefore ttFiber70ReverseSingleStep43

theorem ttFiber70State43_in_pass2_full :
    ttFiber70StateAt 43 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix43 ++ [ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix43 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 43) ttFiber70State43_in_pass2_prefix43

theorem ttFiber70State44_in_pass2_prefix44 :
    ttFiber70StateAt 44 ∈ chainClosureStep ttWord ttFiber70Prefix44 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 40 ∈
      chainClosureStep ttWord ttFiber70Prefix43 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix43 = ttFiber70Prefix40 ++ [ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43]
      (chainClosureStep ttWord ttFiber70Prefix40 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 40) ttFiber70State40_in_pass2_prefix40
  rw [show ttFiber70Prefix44 = ttFiber70Prefix43 ++ [ttFiber70StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 44) []
    (chainClosureStep ttWord ttFiber70Prefix43 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 40) hparentBefore ttFiber70ReverseSingleStep44

theorem ttFiber70State44_in_pass2_full :
    ttFiber70StateAt 44 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix44 ++ [ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix44 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 44) ttFiber70State44_in_pass2_prefix44

theorem ttFiber70State45_in_pass2_prefix45 :
    ttFiber70StateAt 45 ∈ chainClosureStep ttWord ttFiber70Prefix45 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 41 ∈
      chainClosureStep ttWord ttFiber70Prefix44 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix44 = ttFiber70Prefix41 ++ [ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44]
      (chainClosureStep ttWord ttFiber70Prefix41 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 41) ttFiber70State41_in_pass2_prefix41
  rw [show ttFiber70Prefix45 = ttFiber70Prefix44 ++ [ttFiber70StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 45) []
    (chainClosureStep ttWord ttFiber70Prefix44 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 41) hparentBefore ttFiber70ReverseSingleStep45

theorem ttFiber70State45_in_pass2_full :
    ttFiber70StateAt 45 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix45 ++ [ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix45 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 45) ttFiber70State45_in_pass2_prefix45

theorem ttFiber70State46_in_pass2_prefix46 :
    ttFiber70StateAt 46 ∈ chainClosureStep ttWord ttFiber70Prefix46 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 62 ∈
      chainClosureStep ttWord ttFiber70Prefix45 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix45
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 62) ttFiber70State62_in_pass1_full
  rw [show ttFiber70Prefix46 = ttFiber70Prefix45 ++ [ttFiber70StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 46) []
    (chainClosureStep ttWord ttFiber70Prefix45 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 62) hparentBefore ttFiber70ReverseSingleStep46

theorem ttFiber70State46_in_pass2_full :
    ttFiber70StateAt 46 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix46 ++ [ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix46 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 46) ttFiber70State46_in_pass2_prefix46

theorem ttFiber70State47_in_pass2_prefix47 :
    ttFiber70StateAt 47 ∈ chainClosureStep ttWord ttFiber70Prefix47 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 63 ∈
      chainClosureStep ttWord ttFiber70Prefix46 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber70Prefix46
      (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) (ttFiber70StateAt 63) ttFiber70State63_in_pass1_full
  rw [show ttFiber70Prefix47 = ttFiber70Prefix46 ++ [ttFiber70StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 47) []
    (chainClosureStep ttWord ttFiber70Prefix46 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 63) hparentBefore ttFiber70ReverseSingleStep47

theorem ttFiber70State47_in_pass2_full :
    ttFiber70StateAt 47 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix47 ++ [ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix47 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 47) ttFiber70State47_in_pass2_prefix47

theorem ttFiber70State53_in_pass2_prefix53 :
    ttFiber70StateAt 53 ∈ chainClosureStep ttWord ttFiber70Prefix53 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 13 ∈
      chainClosureStep ttWord ttFiber70Prefix52 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix52 = ttFiber70Prefix13 ++ [ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52]
      (chainClosureStep ttWord ttFiber70Prefix13 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 13) ttFiber70State13_in_pass2_prefix13
  rw [show ttFiber70Prefix53 = ttFiber70Prefix52 ++ [ttFiber70StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 53) []
    (chainClosureStep ttWord ttFiber70Prefix52 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 13) hparentBefore ttFiber70ReverseSingleStep53

theorem ttFiber70State53_in_pass2_full :
    ttFiber70StateAt 53 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix53 ++ [ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60, ttFiber70StateAt 61, ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix53 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 53) ttFiber70State53_in_pass2_prefix53

theorem ttFiber70State61_in_pass2_prefix61 :
    ttFiber70StateAt 61 ∈ chainClosureStep ttWord ttFiber70Prefix61 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  have hparentBefore : ttFiber70StateAt 5 ∈
      chainClosureStep ttWord ttFiber70Prefix60 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
    rw [show ttFiber70Prefix60 = ttFiber70Prefix5 ++ [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 6, ttFiber70StateAt 7, ttFiber70StateAt 8, ttFiber70StateAt 9, ttFiber70StateAt 10, ttFiber70StateAt 11, ttFiber70StateAt 12, ttFiber70StateAt 13, ttFiber70StateAt 14, ttFiber70StateAt 15, ttFiber70StateAt 16, ttFiber70StateAt 17, ttFiber70StateAt 18, ttFiber70StateAt 19, ttFiber70StateAt 20, ttFiber70StateAt 21, ttFiber70StateAt 22, ttFiber70StateAt 23, ttFiber70StateAt 24, ttFiber70StateAt 25, ttFiber70StateAt 26, ttFiber70StateAt 27, ttFiber70StateAt 28, ttFiber70StateAt 29, ttFiber70StateAt 30, ttFiber70StateAt 31, ttFiber70StateAt 32, ttFiber70StateAt 33, ttFiber70StateAt 34, ttFiber70StateAt 35, ttFiber70StateAt 36, ttFiber70StateAt 37, ttFiber70StateAt 38, ttFiber70StateAt 39, ttFiber70StateAt 40, ttFiber70StateAt 41, ttFiber70StateAt 42, ttFiber70StateAt 43, ttFiber70StateAt 44, ttFiber70StateAt 45, ttFiber70StateAt 46, ttFiber70StateAt 47, ttFiber70StateAt 48, ttFiber70StateAt 49, ttFiber70StateAt 50, ttFiber70StateAt 51, ttFiber70StateAt 52, ttFiber70StateAt 53, ttFiber70StateAt 54, ttFiber70StateAt 55, ttFiber70StateAt 56, ttFiber70StateAt 57, ttFiber70StateAt 58, ttFiber70StateAt 59, ttFiber70StateAt 60]
      (chainClosureStep ttWord ttFiber70Prefix5 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
      (ttFiber70StateAt 5) ttFiber70State5_in_pass2_prefix5
  rw [show ttFiber70Prefix61 = ttFiber70Prefix60 ++ [ttFiber70StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber70StateAt 61) []
    (chainClosureStep ttWord ttFiber70Prefix60 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 5) hparentBefore ttFiber70ReverseSingleStep61

theorem ttFiber70State61_in_pass2_full :
    ttFiber70StateAt 61 ∈ chainClosureStep ttWord ttFiber70DirectStates (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]) := by
  rw [show ttFiber70DirectStates = ttFiber70Prefix61 ++ [ttFiber70StateAt 62, ttFiber70StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber70StateAt 62, ttFiber70StateAt 63]
    (chainClosureStep ttWord ttFiber70Prefix61 (chainClosureStep ttWord ttFiber70DirectStates [ttFiber70StateAt 0]))
    (ttFiber70StateAt 61) ttFiber70State61_in_pass2_prefix61

theorem ttFiber70State0_in_close :
    ttFiber70StateAt 0 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber70DirectStates
    ttFiber70DirectStates.length [ttFiber70StateAt 0] (ttFiber70StateAt 0) (by simp)

theorem ttFiber70State1_in_close :
    ttFiber70StateAt 1 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 1 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 1) ttFiber70State1_in_pass1_full

theorem ttFiber70State2_in_close :
    ttFiber70StateAt 2 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 2 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 2) ttFiber70State2_in_pass1_full

theorem ttFiber70State3_in_close :
    ttFiber70StateAt 3 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 3 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 3) ttFiber70State3_in_pass1_full

theorem ttFiber70State4_in_close :
    ttFiber70StateAt 4 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 4 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 4) ttFiber70State4_in_pass1_full

theorem ttFiber70State5_in_close :
    ttFiber70StateAt 5 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 5 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 5) ttFiber70FirstPassGrows
    ttFiber70State5_in_pass2_full

theorem ttFiber70State6_in_close :
    ttFiber70StateAt 6 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 6 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 6) ttFiber70State6_in_pass1_full

theorem ttFiber70State7_in_close :
    ttFiber70StateAt 7 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 7 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 7) ttFiber70State7_in_pass1_full

theorem ttFiber70State8_in_close :
    ttFiber70StateAt 8 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 8 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 8) ttFiber70State8_in_pass1_full

theorem ttFiber70State9_in_close :
    ttFiber70StateAt 9 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 9 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 9) ttFiber70State9_in_pass1_full

theorem ttFiber70State10_in_close :
    ttFiber70StateAt 10 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 10 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 10) ttFiber70State10_in_pass1_full

theorem ttFiber70State11_in_close :
    ttFiber70StateAt 11 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 11 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 11) ttFiber70State11_in_pass1_full

theorem ttFiber70State12_in_close :
    ttFiber70StateAt 12 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 12 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 12) ttFiber70State12_in_pass1_full

theorem ttFiber70State13_in_close :
    ttFiber70StateAt 13 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 13 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 13) ttFiber70FirstPassGrows
    ttFiber70State13_in_pass2_full

theorem ttFiber70State14_in_close :
    ttFiber70StateAt 14 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 14 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 14) ttFiber70State14_in_pass1_full

theorem ttFiber70State15_in_close :
    ttFiber70StateAt 15 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 15 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 15) ttFiber70State15_in_pass1_full

theorem ttFiber70State16_in_close :
    ttFiber70StateAt 16 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 16 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 16) ttFiber70State16_in_pass1_full

theorem ttFiber70State17_in_close :
    ttFiber70StateAt 17 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 17 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 17) ttFiber70State17_in_pass1_full

theorem ttFiber70State18_in_close :
    ttFiber70StateAt 18 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 18 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 18) ttFiber70State18_in_pass1_full

theorem ttFiber70State19_in_close :
    ttFiber70StateAt 19 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 19 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 19) ttFiber70State19_in_pass1_full

theorem ttFiber70State20_in_close :
    ttFiber70StateAt 20 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 20 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 20) ttFiber70State20_in_pass1_full

theorem ttFiber70State21_in_close :
    ttFiber70StateAt 21 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 21 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 21) ttFiber70State21_in_pass1_full

theorem ttFiber70State22_in_close :
    ttFiber70StateAt 22 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 22 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 22) ttFiber70State22_in_pass1_full

theorem ttFiber70State23_in_close :
    ttFiber70StateAt 23 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 23 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 23) ttFiber70State23_in_pass1_full

theorem ttFiber70State24_in_close :
    ttFiber70StateAt 24 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 24 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 24) ttFiber70State24_in_pass1_full

theorem ttFiber70State25_in_close :
    ttFiber70StateAt 25 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 25 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 25) ttFiber70State25_in_pass1_full

theorem ttFiber70State26_in_close :
    ttFiber70StateAt 26 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 26 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 26) ttFiber70State26_in_pass1_full

theorem ttFiber70State27_in_close :
    ttFiber70StateAt 27 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 27 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 27) ttFiber70State27_in_pass1_full

theorem ttFiber70State28_in_close :
    ttFiber70StateAt 28 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 28 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 28) ttFiber70State28_in_pass1_full

theorem ttFiber70State29_in_close :
    ttFiber70StateAt 29 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 29 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 29) ttFiber70State29_in_pass1_full

theorem ttFiber70State30_in_close :
    ttFiber70StateAt 30 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 30 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 30) ttFiber70State30_in_pass1_full

theorem ttFiber70State31_in_close :
    ttFiber70StateAt 31 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 31 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 31) ttFiber70State31_in_pass1_full

theorem ttFiber70State32_in_close :
    ttFiber70StateAt 32 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 32 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 32) ttFiber70FirstPassGrows
    ttFiber70State32_in_pass2_full

theorem ttFiber70State33_in_close :
    ttFiber70StateAt 33 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 33 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 33) ttFiber70FirstPassGrows
    ttFiber70State33_in_pass2_full

theorem ttFiber70State34_in_close :
    ttFiber70StateAt 34 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 34 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 34) ttFiber70State34_in_pass1_full

theorem ttFiber70State35_in_close :
    ttFiber70StateAt 35 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 35 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 35) ttFiber70State35_in_pass1_full

theorem ttFiber70State36_in_close :
    ttFiber70StateAt 36 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 36 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 36) ttFiber70State36_in_pass1_full

theorem ttFiber70State37_in_close :
    ttFiber70StateAt 37 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 37 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 37) ttFiber70FirstPassGrows
    ttFiber70State37_in_pass2_full

theorem ttFiber70State38_in_close :
    ttFiber70StateAt 38 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 38 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 38) ttFiber70State38_in_pass1_full

theorem ttFiber70State39_in_close :
    ttFiber70StateAt 39 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 39 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 39) ttFiber70State39_in_pass1_full

theorem ttFiber70State40_in_close :
    ttFiber70StateAt 40 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 40 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 40) ttFiber70FirstPassGrows
    ttFiber70State40_in_pass2_full

theorem ttFiber70State41_in_close :
    ttFiber70StateAt 41 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 41 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 41) ttFiber70FirstPassGrows
    ttFiber70State41_in_pass2_full

theorem ttFiber70State42_in_close :
    ttFiber70StateAt 42 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 42 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 42) ttFiber70FirstPassGrows
    ttFiber70State42_in_pass2_full

theorem ttFiber70State43_in_close :
    ttFiber70StateAt 43 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 43 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 43) ttFiber70FirstPassGrows
    ttFiber70State43_in_pass2_full

theorem ttFiber70State44_in_close :
    ttFiber70StateAt 44 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 44 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 44) ttFiber70FirstPassGrows
    ttFiber70State44_in_pass2_full

theorem ttFiber70State45_in_close :
    ttFiber70StateAt 45 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 45 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 45) ttFiber70FirstPassGrows
    ttFiber70State45_in_pass2_full

theorem ttFiber70State46_in_close :
    ttFiber70StateAt 46 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 46 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 46) ttFiber70FirstPassGrows
    ttFiber70State46_in_pass2_full

theorem ttFiber70State47_in_close :
    ttFiber70StateAt 47 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 47 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 47) ttFiber70FirstPassGrows
    ttFiber70State47_in_pass2_full

theorem ttFiber70State48_in_close :
    ttFiber70StateAt 48 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 48 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 48) ttFiber70State48_in_pass1_full

theorem ttFiber70State49_in_close :
    ttFiber70StateAt 49 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 49 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 49) ttFiber70State49_in_pass1_full

theorem ttFiber70State50_in_close :
    ttFiber70StateAt 50 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 50 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 50) ttFiber70State50_in_pass1_full

theorem ttFiber70State51_in_close :
    ttFiber70StateAt 51 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 51 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 51) ttFiber70State51_in_pass1_full

theorem ttFiber70State52_in_close :
    ttFiber70StateAt 52 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 52 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 52) ttFiber70State52_in_pass1_full

theorem ttFiber70State53_in_close :
    ttFiber70StateAt 53 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 53 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 53) ttFiber70FirstPassGrows
    ttFiber70State53_in_pass2_full

theorem ttFiber70State54_in_close :
    ttFiber70StateAt 54 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 54 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 54) ttFiber70State54_in_pass1_full

theorem ttFiber70State55_in_close :
    ttFiber70StateAt 55 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 55 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 55) ttFiber70State55_in_pass1_full

theorem ttFiber70State56_in_close :
    ttFiber70StateAt 56 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 56 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 56) ttFiber70State56_in_pass1_full

theorem ttFiber70State57_in_close :
    ttFiber70StateAt 57 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 57 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 57) ttFiber70State57_in_pass1_full

theorem ttFiber70State58_in_close :
    ttFiber70StateAt 58 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 58 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 58) ttFiber70State58_in_pass1_full

theorem ttFiber70State59_in_close :
    ttFiber70StateAt 59 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 59 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 59) ttFiber70State59_in_pass1_full

theorem ttFiber70State60_in_close :
    ttFiber70StateAt 60 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 60 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 60) ttFiber70State60_in_pass1_full

theorem ttFiber70State61_in_close :
    ttFiber70StateAt 61 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 61 ∈ closeChainFiber ttWord ttFiber70DirectStates (62 + 2)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber70DirectStates 62
    [ttFiber70StateAt 0] (ttFiber70StateAt 61) ttFiber70FirstPassGrows
    ttFiber70State61_in_pass2_full

theorem ttFiber70State62_in_close :
    ttFiber70StateAt 62 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 62 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 62) ttFiber70State62_in_pass1_full

theorem ttFiber70State63_in_close :
    ttFiber70StateAt 63 ∈
      closeChainFiber ttWord ttFiber70DirectStates ttFiber70DirectStates.length
        [ttFiber70StateAt 0] := by
  change ttFiber70StateAt 63 ∈ closeChainFiber ttWord ttFiber70DirectStates (63 + 1)
    [ttFiber70StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber70DirectStates 63
    [ttFiber70StateAt 0] (ttFiber70StateAt 63) ttFiber70State63_in_pass1_full

theorem ttFiber70DirectConnected :
    chainFiberConnected ttWord ttFiber70DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber70DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber70State0_in_close
  · subst state
    exact ttFiber70State1_in_close
  · subst state
    exact ttFiber70State2_in_close
  · subst state
    exact ttFiber70State3_in_close
  · subst state
    exact ttFiber70State4_in_close
  · subst state
    exact ttFiber70State5_in_close
  · subst state
    exact ttFiber70State6_in_close
  · subst state
    exact ttFiber70State7_in_close
  · subst state
    exact ttFiber70State8_in_close
  · subst state
    exact ttFiber70State9_in_close
  · subst state
    exact ttFiber70State10_in_close
  · subst state
    exact ttFiber70State11_in_close
  · subst state
    exact ttFiber70State12_in_close
  · subst state
    exact ttFiber70State13_in_close
  · subst state
    exact ttFiber70State14_in_close
  · subst state
    exact ttFiber70State15_in_close
  · subst state
    exact ttFiber70State16_in_close
  · subst state
    exact ttFiber70State17_in_close
  · subst state
    exact ttFiber70State18_in_close
  · subst state
    exact ttFiber70State19_in_close
  · subst state
    exact ttFiber70State20_in_close
  · subst state
    exact ttFiber70State21_in_close
  · subst state
    exact ttFiber70State22_in_close
  · subst state
    exact ttFiber70State23_in_close
  · subst state
    exact ttFiber70State24_in_close
  · subst state
    exact ttFiber70State25_in_close
  · subst state
    exact ttFiber70State26_in_close
  · subst state
    exact ttFiber70State27_in_close
  · subst state
    exact ttFiber70State28_in_close
  · subst state
    exact ttFiber70State29_in_close
  · subst state
    exact ttFiber70State30_in_close
  · subst state
    exact ttFiber70State31_in_close
  · subst state
    exact ttFiber70State32_in_close
  · subst state
    exact ttFiber70State33_in_close
  · subst state
    exact ttFiber70State34_in_close
  · subst state
    exact ttFiber70State35_in_close
  · subst state
    exact ttFiber70State36_in_close
  · subst state
    exact ttFiber70State37_in_close
  · subst state
    exact ttFiber70State38_in_close
  · subst state
    exact ttFiber70State39_in_close
  · subst state
    exact ttFiber70State40_in_close
  · subst state
    exact ttFiber70State41_in_close
  · subst state
    exact ttFiber70State42_in_close
  · subst state
    exact ttFiber70State43_in_close
  · subst state
    exact ttFiber70State44_in_close
  · subst state
    exact ttFiber70State45_in_close
  · subst state
    exact ttFiber70State46_in_close
  · subst state
    exact ttFiber70State47_in_close
  · subst state
    exact ttFiber70State48_in_close
  · subst state
    exact ttFiber70State49_in_close
  · subst state
    exact ttFiber70State50_in_close
  · subst state
    exact ttFiber70State51_in_close
  · subst state
    exact ttFiber70State52_in_close
  · subst state
    exact ttFiber70State53_in_close
  · subst state
    exact ttFiber70State54_in_close
  · subst state
    exact ttFiber70State55_in_close
  · subst state
    exact ttFiber70State56_in_close
  · subst state
    exact ttFiber70State57_in_close
  · subst state
    exact ttFiber70State58_in_close
  · subst state
    exact ttFiber70State59_in_close
  · subst state
    exact ttFiber70State60_in_close
  · subst state
    exact ttFiber70State61_in_close
  · subst state
    exact ttFiber70State62_in_close
  · subst state
    exact ttFiber70State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
