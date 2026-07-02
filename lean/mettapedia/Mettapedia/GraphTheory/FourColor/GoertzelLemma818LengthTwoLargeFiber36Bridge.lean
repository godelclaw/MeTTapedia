import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber36

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber36StateAt (i : Nat) : List TauState :=
  directStates (ttFiber36RowAt i).sourceLeft (ttFiber36RowAt i).sourceRight

def ttFiber36DirectStates : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]

def ttFiber36Prefix0 : List (List TauState) :=
  [ttFiber36StateAt 0]

def ttFiber36Prefix1 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1]

def ttFiber36Prefix2 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2]

def ttFiber36Prefix3 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3]

def ttFiber36Prefix4 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4]

def ttFiber36Prefix5 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5]

def ttFiber36Prefix6 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6]

def ttFiber36Prefix7 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7]

def ttFiber36Prefix8 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8]

def ttFiber36Prefix9 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9]

def ttFiber36Prefix10 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10]

def ttFiber36Prefix11 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11]

def ttFiber36Prefix12 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12]

def ttFiber36Prefix13 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13]

def ttFiber36Prefix14 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14]

def ttFiber36Prefix15 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15]

def ttFiber36Prefix16 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16]

def ttFiber36Prefix17 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17]

def ttFiber36Prefix18 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18]

def ttFiber36Prefix19 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19]

def ttFiber36Prefix20 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20]

def ttFiber36Prefix21 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21]

def ttFiber36Prefix22 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22]

def ttFiber36Prefix23 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23]

def ttFiber36Prefix24 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24]

def ttFiber36Prefix25 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25]

def ttFiber36Prefix26 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26]

def ttFiber36Prefix27 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27]

def ttFiber36Prefix28 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28]

def ttFiber36Prefix29 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29]

def ttFiber36Prefix30 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30]

def ttFiber36Prefix31 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31]

def ttFiber36Prefix32 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32]

def ttFiber36Prefix33 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33]

def ttFiber36Prefix34 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34]

def ttFiber36Prefix35 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35]

def ttFiber36Prefix36 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36]

def ttFiber36Prefix37 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37]

def ttFiber36Prefix38 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38]

def ttFiber36Prefix39 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39]

def ttFiber36Prefix40 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40]

def ttFiber36Prefix41 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41]

def ttFiber36Prefix42 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42]

def ttFiber36Prefix43 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43]

def ttFiber36Prefix44 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44]

def ttFiber36Prefix45 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45]

def ttFiber36Prefix46 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46]

def ttFiber36Prefix47 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47]

def ttFiber36Prefix48 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48]

def ttFiber36Prefix49 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49]

def ttFiber36Prefix50 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50]

def ttFiber36Prefix51 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51]

def ttFiber36Prefix52 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52]

def ttFiber36Prefix53 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53]

def ttFiber36Prefix54 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54]

def ttFiber36Prefix55 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55]

def ttFiber36Prefix56 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56]

def ttFiber36Prefix57 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57]

def ttFiber36Prefix58 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58]

def ttFiber36Prefix59 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59]

def ttFiber36Prefix60 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60]

def ttFiber36Prefix61 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61]

def ttFiber36Prefix62 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62]

def ttFiber36Prefix63 : List (List TauState) :=
  [ttFiber36StateAt 0, ttFiber36StateAt 1, ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]

theorem ttFiber36ReverseRow_1_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk0] at h
  exact h.2

theorem ttFiber36ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 1)
      (ttFiber36RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 1) (by decide) ttFiber36ReverseRow_1_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_2_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk1] at h
  exact h.1

theorem ttFiber36ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 2)
      (ttFiber36RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 2) (by decide) ttFiber36ReverseRow_2_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_3_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk1] at h
  exact h.2

theorem ttFiber36ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 3)
      (ttFiber36RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 3) (by decide) ttFiber36ReverseRow_3_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_4_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk2] at h
  exact h.1

theorem ttFiber36ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 4)
      (ttFiber36RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 4) (by decide) ttFiber36ReverseRow_4_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_5_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk2] at h
  exact h.2

theorem ttFiber36ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 5)
      (ttFiber36RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 5) (by decide) ttFiber36ReverseRow_5_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_6_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk3] at h
  exact h.1

theorem ttFiber36ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 6)
      (ttFiber36RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 6) (by decide) ttFiber36ReverseRow_6_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_7_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk3] at h
  exact h.2

theorem ttFiber36ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 7)
      (ttFiber36RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 7) (by decide) ttFiber36ReverseRow_7_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_8_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk4] at h
  exact h.1

theorem ttFiber36ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 8)
      (ttFiber36RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 8) (by decide) ttFiber36ReverseRow_8_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_9_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk4] at h
  exact h.2

theorem ttFiber36ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 9)
      (ttFiber36RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 9) (by decide) ttFiber36ReverseRow_9_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_10_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk5] at h
  exact h.1

theorem ttFiber36ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 10)
      (ttFiber36RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 10) (by decide) ttFiber36ReverseRow_10_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_11_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk5] at h
  exact h.2

theorem ttFiber36ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 3) (ttFiber36StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 3) (ttFiber36StateAt 11)
      (ttFiber36RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 11) (by decide) ttFiber36ReverseRow_11_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_12_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk6] at h
  exact h.1

theorem ttFiber36ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 4) (ttFiber36StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 4) (ttFiber36StateAt 12)
      (ttFiber36RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 12) (by decide) ttFiber36ReverseRow_12_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_13_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk6] at h
  exact h.2

theorem ttFiber36ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 5) (ttFiber36StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 5) (ttFiber36StateAt 13)
      (ttFiber36RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 13) (by decide) ttFiber36ReverseRow_13_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_14_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk7] at h
  exact h.1

theorem ttFiber36ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 14)
      (ttFiber36RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 14) (by decide) ttFiber36ReverseRow_14_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_15_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk7] at h
  exact h.2

theorem ttFiber36ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 15)
      (ttFiber36RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 15) (by decide) ttFiber36ReverseRow_15_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_16_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk8] at h
  exact h.1

theorem ttFiber36ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 16)
      (ttFiber36RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 16) (by decide) ttFiber36ReverseRow_16_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_17_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk8] at h
  exact h.2

theorem ttFiber36ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 17)
      (ttFiber36RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 17) (by decide) ttFiber36ReverseRow_17_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_18_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk9] at h
  exact h.1

theorem ttFiber36ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 18)
      (ttFiber36RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 18) (by decide) ttFiber36ReverseRow_18_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_19_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk9] at h
  exact h.2

theorem ttFiber36ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 3) (ttFiber36StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 3) (ttFiber36StateAt 19)
      (ttFiber36RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 19) (by decide) ttFiber36ReverseRow_19_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_20_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk10] at h
  exact h.1

theorem ttFiber36ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 16) (ttFiber36StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 16) (ttFiber36StateAt 20)
      (ttFiber36RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 20) (by decide) ttFiber36ReverseRow_20_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_21_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk10] at h
  exact h.2

theorem ttFiber36ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 17) (ttFiber36StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 17) (ttFiber36StateAt 21)
      (ttFiber36RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 21) (by decide) ttFiber36ReverseRow_21_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_22_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk11] at h
  exact h.1

theorem ttFiber36ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 22)
      (ttFiber36RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 22) (by decide) ttFiber36ReverseRow_22_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_23_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk11] at h
  exact h.2

theorem ttFiber36ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 23)
      (ttFiber36RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 23) (by decide) ttFiber36ReverseRow_23_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_24_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk12] at h
  exact h.1

theorem ttFiber36ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 8) (ttFiber36StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 8) (ttFiber36StateAt 24)
      (ttFiber36RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 24) (by decide) ttFiber36ReverseRow_24_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_25_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk12] at h
  exact h.2

theorem ttFiber36ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 9) (ttFiber36StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 9) (ttFiber36StateAt 25)
      (ttFiber36RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 25) (by decide) ttFiber36ReverseRow_25_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_26_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk13] at h
  exact h.1

theorem ttFiber36ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 10) (ttFiber36StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 10) (ttFiber36StateAt 26)
      (ttFiber36RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 26) (by decide) ttFiber36ReverseRow_26_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_27_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk13] at h
  exact h.2

theorem ttFiber36ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 11) (ttFiber36StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 11) (ttFiber36StateAt 27)
      (ttFiber36RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 27) (by decide) ttFiber36ReverseRow_27_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_28_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk14] at h
  exact h.1

theorem ttFiber36ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 24) (ttFiber36StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 24) (ttFiber36StateAt 28)
      (ttFiber36RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 28) (by decide) ttFiber36ReverseRow_28_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_29_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk14] at h
  exact h.2

theorem ttFiber36ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 25) (ttFiber36StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 25) (ttFiber36StateAt 29)
      (ttFiber36RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 29) (by decide) ttFiber36ReverseRow_29_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_30_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk15] at h
  exact h.1

theorem ttFiber36ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 14) (ttFiber36StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 14) (ttFiber36StateAt 30)
      (ttFiber36RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 30) (by decide) ttFiber36ReverseRow_30_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_31_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk15] at h
  exact h.2

theorem ttFiber36ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 15) (ttFiber36StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 15) (ttFiber36StateAt 31)
      (ttFiber36RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 31) (by decide) ttFiber36ReverseRow_31_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_32_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk16] at h
  exact h.1

theorem ttFiber36ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 0) (ttFiber36StateAt 32)
      (ttFiber36RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 32) (by decide) ttFiber36ReverseRow_32_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_33_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk16] at h
  exact h.2

theorem ttFiber36ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 1) (ttFiber36StateAt 33)
      (ttFiber36RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 33) (by decide) ttFiber36ReverseRow_33_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_34_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk17] at h
  exact h.1

theorem ttFiber36ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 2) (ttFiber36StateAt 34)
      (ttFiber36RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 34) (by decide) ttFiber36ReverseRow_34_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_35_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk17] at h
  exact h.2

theorem ttFiber36ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 35)
      (ttFiber36RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 35) (by decide) ttFiber36ReverseRow_35_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_36_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk18] at h
  exact h.1

theorem ttFiber36ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 36)
      (ttFiber36RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 36) (by decide) ttFiber36ReverseRow_36_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_37_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk18] at h
  exact h.2

theorem ttFiber36ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 33) (ttFiber36StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 33) (ttFiber36StateAt 37)
      (ttFiber36RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 37) (by decide) ttFiber36ReverseRow_37_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_38_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk19] at h
  exact h.1

theorem ttFiber36ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 6) (ttFiber36StateAt 38)
      (ttFiber36RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 38) (by decide) ttFiber36ReverseRow_38_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_39_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk19] at h
  exact h.2

theorem ttFiber36ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 7) (ttFiber36StateAt 39)
      (ttFiber36RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 39) (by decide) ttFiber36ReverseRow_39_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_40_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk20] at h
  exact h.1

theorem ttFiber36ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 8) (ttFiber36StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 8) (ttFiber36StateAt 40)
      (ttFiber36RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 40) (by decide) ttFiber36ReverseRow_40_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_41_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk20] at h
  exact h.2

theorem ttFiber36ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 9) (ttFiber36StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 9) (ttFiber36StateAt 41)
      (ttFiber36RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 41) (by decide) ttFiber36ReverseRow_41_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_42_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk21] at h
  exact h.1

theorem ttFiber36ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 10) (ttFiber36StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 10) (ttFiber36StateAt 42)
      (ttFiber36RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 42) (by decide) ttFiber36ReverseRow_42_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_43_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk21] at h
  exact h.2

theorem ttFiber36ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 43)
      (ttFiber36RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 43) (by decide) ttFiber36ReverseRow_43_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_44_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk22] at h
  exact h.1

theorem ttFiber36ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 44)
      (ttFiber36RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 44) (by decide) ttFiber36ReverseRow_44_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_45_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk22] at h
  exact h.2

theorem ttFiber36ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 41) (ttFiber36StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 41) (ttFiber36StateAt 45)
      (ttFiber36RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 45) (by decide) ttFiber36ReverseRow_45_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_46_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk23] at h
  exact h.1

theorem ttFiber36ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 14) (ttFiber36StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 14) (ttFiber36StateAt 46)
      (ttFiber36RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 46) (by decide) ttFiber36ReverseRow_46_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_47_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk23] at h
  exact h.2

theorem ttFiber36ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 15) (ttFiber36StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 15) (ttFiber36StateAt 47)
      (ttFiber36RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 47) (by decide) ttFiber36ReverseRow_47_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_48_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk24] at h
  exact h.1

theorem ttFiber36ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 16) (ttFiber36StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 16) (ttFiber36StateAt 48)
      (ttFiber36RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 48) (by decide) ttFiber36ReverseRow_48_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_49_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk24] at h
  exact h.2

theorem ttFiber36ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 17) (ttFiber36StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 17) (ttFiber36StateAt 49)
      (ttFiber36RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 49) (by decide) ttFiber36ReverseRow_49_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_50_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk25] at h
  exact h.1

theorem ttFiber36ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 18) (ttFiber36StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 18) (ttFiber36StateAt 50)
      (ttFiber36RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 50) (by decide) ttFiber36ReverseRow_50_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_51_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk25] at h
  exact h.2

theorem ttFiber36ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 19) (ttFiber36StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 19) (ttFiber36StateAt 51)
      (ttFiber36RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 51) (by decide) ttFiber36ReverseRow_51_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_52_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk26] at h
  exact h.1

theorem ttFiber36ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 40) (ttFiber36StateAt 52)
      (ttFiber36RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 52) (by decide) ttFiber36ReverseRow_52_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_53_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk26] at h
  exact h.2

theorem ttFiber36ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 41) (ttFiber36StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 41) (ttFiber36StateAt 53)
      (ttFiber36RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 53) (by decide) ttFiber36ReverseRow_53_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_54_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk27] at h
  exact h.1

theorem ttFiber36ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 22) (ttFiber36StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 22) (ttFiber36StateAt 54)
      (ttFiber36RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 54) (by decide) ttFiber36ReverseRow_54_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_55_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk27] at h
  exact h.2

theorem ttFiber36ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 23) (ttFiber36StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 23) (ttFiber36StateAt 55)
      (ttFiber36RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 55) (by decide) ttFiber36ReverseRow_55_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_56_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk28] at h
  exact h.1

theorem ttFiber36ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 39) (ttFiber36StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 39) (ttFiber36StateAt 56)
      (ttFiber36RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 56) (by decide) ttFiber36ReverseRow_56_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_57_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk28] at h
  exact h.2

theorem ttFiber36ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 38) (ttFiber36StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 38) (ttFiber36StateAt 57)
      (ttFiber36RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 57) (by decide) ttFiber36ReverseRow_57_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_58_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk29] at h
  exact h.1

theorem ttFiber36ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 36) (ttFiber36StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 36) (ttFiber36StateAt 58)
      (ttFiber36RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 58) (by decide) ttFiber36ReverseRow_58_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_59_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk29] at h
  exact h.2

theorem ttFiber36ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 37) (ttFiber36StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 37) (ttFiber36StateAt 59)
      (ttFiber36RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 59) (by decide) ttFiber36ReverseRow_59_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_60_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk30] at h
  exact h.1

theorem ttFiber36ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 32) (ttFiber36StateAt 60)
      (ttFiber36RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 60) (by decide) ttFiber36ReverseRow_60_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_61_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk30] at h
  exact h.2

theorem ttFiber36ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 33) (ttFiber36StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 33) (ttFiber36StateAt 61)
      (ttFiber36RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 61) (by decide) ttFiber36ReverseRow_61_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_62_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk31] at h
  exact h.1

theorem ttFiber36ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 34) (ttFiber36StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 34) (ttFiber36StateAt 62)
      (ttFiber36RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 62) (by decide) ttFiber36ReverseRow_62_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36ReverseRow_63_ok' :
    directRowReverseValid ttFiber36Key ttFiber36Expected (ttFiber36RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber36Chunk31] at h
  exact h.2

theorem ttFiber36ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber36StateAt 35) (ttFiber36StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber36StateAt 35) (ttFiber36StateAt 63)
      (ttFiber36RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber36Key ttFiber36Expected
      (ttFiber36RowAt 63) (by decide) ttFiber36ReverseRow_63_ok'
    simpa [ttFiber36StateAt, ttFiber36RowAt, ttFiber36Rows, listGetD, directRow] using h

theorem ttFiber36FirstPassGrows :
    ((chainClosureStep ttWord ttFiber36DirectStates [ttFiber36StateAt 0]).length ==
      [ttFiber36StateAt 0].length) = false := by
  have hroot : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36DirectStates [ttFiber36StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber36DirectStates [ttFiber36StateAt 0]
      (ttFiber36StateAt 0) (by simp)
  have hnew : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36DirectStates [ttFiber36StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber36DirectStates [ttFiber36StateAt 0]
      (ttFiber36StateAt 0) (ttFiber36StateAt 1) (by decide) (by simp)
      ttFiber36ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber36DirectStates [ttFiber36StateAt 0])
    (ttFiber36StateAt 0) (ttFiber36StateAt 1) hroot hnew (by decide)

theorem ttFiber36State0_in_pass0_full :
    ttFiber36StateAt 0 ∈ [ttFiber36StateAt 0] := by
  simp

theorem ttFiber36State0_in_pass1_full :
    ttFiber36StateAt 0 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber36DirectStates
    ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full

theorem ttFiber36State1_in_pass1_prefix1 :
    ttFiber36StateAt 1 ∈ chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix0 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix0
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix1 = ttFiber36Prefix0 ++ [ttFiber36StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 1) []
    (chainClosureStep ttWord ttFiber36Prefix0 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep1

theorem ttFiber36State1_in_pass1_full :
    ttFiber36StateAt 1 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix1 ++ [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1

theorem ttFiber36State2_in_pass1_prefix2 :
    ttFiber36StateAt 2 ∈ chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix1
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix2 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 2) []
    (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep2

theorem ttFiber36State2_in_pass1_full :
    ttFiber36StateAt 2 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix2 ++ [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 2) ttFiber36State2_in_pass1_prefix2

theorem ttFiber36State3_in_pass1_prefix3 :
    ttFiber36StateAt 3 ∈ chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix2 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2]
      (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1
  rw [show ttFiber36Prefix3 = ttFiber36Prefix2 ++ [ttFiber36StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 3) []
    (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) hparentBefore ttFiber36ReverseSingleStep3

theorem ttFiber36State3_in_pass1_full :
    ttFiber36StateAt 3 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix3 ++ [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 3) ttFiber36State3_in_pass1_prefix3

theorem ttFiber36State4_in_pass1_prefix4 :
    ttFiber36StateAt 4 ∈ chainClosureStep ttWord ttFiber36Prefix4 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 2 ∈
      chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix3 = ttFiber36Prefix2 ++ [ttFiber36StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 3]
      (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 2) ttFiber36State2_in_pass1_prefix2
  rw [show ttFiber36Prefix4 = ttFiber36Prefix3 ++ [ttFiber36StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 4) []
    (chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 2) hparentBefore ttFiber36ReverseSingleStep4

theorem ttFiber36State4_in_pass1_full :
    ttFiber36StateAt 4 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix4 ++ [ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix4 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 4) ttFiber36State4_in_pass1_prefix4

theorem ttFiber36State6_in_pass1_prefix6 :
    ttFiber36StateAt 6 ∈ chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36Prefix5 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix5 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5]
      (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1
  rw [show ttFiber36Prefix6 = ttFiber36Prefix5 ++ [ttFiber36StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 6) []
    (chainClosureStep ttWord ttFiber36Prefix5 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) hparentBefore ttFiber36ReverseSingleStep6

theorem ttFiber36State6_in_pass1_full :
    ttFiber36StateAt 6 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix6 ++ [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 6) ttFiber36State6_in_pass1_prefix6

theorem ttFiber36State7_in_pass1_prefix7 :
    ttFiber36StateAt 7 ∈ chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix6
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix7 = ttFiber36Prefix6 ++ [ttFiber36StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 7) []
    (chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep7

theorem ttFiber36State7_in_pass1_full :
    ttFiber36StateAt 7 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix7 ++ [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 7) ttFiber36State7_in_pass1_prefix7

theorem ttFiber36State8_in_pass1_prefix8 :
    ttFiber36StateAt 8 ∈ chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix7
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix8 = ttFiber36Prefix7 ++ [ttFiber36StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 8) []
    (chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep8

theorem ttFiber36State8_in_pass1_full :
    ttFiber36StateAt 8 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix8 ++ [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 8) ttFiber36State8_in_pass1_prefix8

theorem ttFiber36State9_in_pass1_prefix9 :
    ttFiber36StateAt 9 ∈ chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix8 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8]
      (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1
  rw [show ttFiber36Prefix9 = ttFiber36Prefix8 ++ [ttFiber36StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 9) []
    (chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) hparentBefore ttFiber36ReverseSingleStep9

theorem ttFiber36State9_in_pass1_full :
    ttFiber36StateAt 9 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix9 ++ [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 9) ttFiber36State9_in_pass1_prefix9

theorem ttFiber36State10_in_pass1_prefix10 :
    ttFiber36StateAt 10 ∈ chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 2 ∈
      chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix9 = ttFiber36Prefix2 ++ [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9]
      (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 2) ttFiber36State2_in_pass1_prefix2
  rw [show ttFiber36Prefix10 = ttFiber36Prefix9 ++ [ttFiber36StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 10) []
    (chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 2) hparentBefore ttFiber36ReverseSingleStep10

theorem ttFiber36State10_in_pass1_full :
    ttFiber36StateAt 10 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix10 ++ [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 10) ttFiber36State10_in_pass1_prefix10

theorem ttFiber36State11_in_pass1_prefix11 :
    ttFiber36StateAt 11 ∈ chainClosureStep ttWord ttFiber36Prefix11 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 3 ∈
      chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix10 = ttFiber36Prefix3 ++ [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10]
      (chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 3) ttFiber36State3_in_pass1_prefix3
  rw [show ttFiber36Prefix11 = ttFiber36Prefix10 ++ [ttFiber36StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 11) []
    (chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 3) hparentBefore ttFiber36ReverseSingleStep11

theorem ttFiber36State11_in_pass1_full :
    ttFiber36StateAt 11 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix11 ++ [ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix11 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 11) ttFiber36State11_in_pass1_prefix11

theorem ttFiber36State12_in_pass1_prefix12 :
    ttFiber36StateAt 12 ∈ chainClosureStep ttWord ttFiber36Prefix12 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 4 ∈
      chainClosureStep ttWord ttFiber36Prefix11 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix11 = ttFiber36Prefix4 ++ [ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11]
      (chainClosureStep ttWord ttFiber36Prefix4 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 4) ttFiber36State4_in_pass1_prefix4
  rw [show ttFiber36Prefix12 = ttFiber36Prefix11 ++ [ttFiber36StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 12) []
    (chainClosureStep ttWord ttFiber36Prefix11 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 4) hparentBefore ttFiber36ReverseSingleStep12

theorem ttFiber36State12_in_pass1_full :
    ttFiber36StateAt 12 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix12 ++ [ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix12 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 12) ttFiber36State12_in_pass1_prefix12

theorem ttFiber36State14_in_pass1_prefix14 :
    ttFiber36StateAt 14 ∈ chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 6 ∈
      chainClosureStep ttWord ttFiber36Prefix13 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix13 = ttFiber36Prefix6 ++ [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13]
      (chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 6) ttFiber36State6_in_pass1_prefix6
  rw [show ttFiber36Prefix14 = ttFiber36Prefix13 ++ [ttFiber36StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 14) []
    (chainClosureStep ttWord ttFiber36Prefix13 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 6) hparentBefore ttFiber36ReverseSingleStep14

theorem ttFiber36State14_in_pass1_full :
    ttFiber36StateAt 14 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix14 ++ [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 14) ttFiber36State14_in_pass1_prefix14

theorem ttFiber36State15_in_pass1_prefix15 :
    ttFiber36StateAt 15 ∈ chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 7 ∈
      chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix14 = ttFiber36Prefix7 ++ [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14]
      (chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 7) ttFiber36State7_in_pass1_prefix7
  rw [show ttFiber36Prefix15 = ttFiber36Prefix14 ++ [ttFiber36StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 15) []
    (chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 7) hparentBefore ttFiber36ReverseSingleStep15

theorem ttFiber36State15_in_pass1_full :
    ttFiber36StateAt 15 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix15 ++ [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 15) ttFiber36State15_in_pass1_prefix15

theorem ttFiber36State16_in_pass1_prefix16 :
    ttFiber36StateAt 16 ∈ chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix15
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix16 = ttFiber36Prefix15 ++ [ttFiber36StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 16) []
    (chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep16

theorem ttFiber36State16_in_pass1_full :
    ttFiber36StateAt 16 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix16 ++ [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 16) ttFiber36State16_in_pass1_prefix16

theorem ttFiber36State17_in_pass1_prefix17 :
    ttFiber36StateAt 17 ∈ chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix16 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16]
      (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1
  rw [show ttFiber36Prefix17 = ttFiber36Prefix16 ++ [ttFiber36StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 17) []
    (chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) hparentBefore ttFiber36ReverseSingleStep17

theorem ttFiber36State17_in_pass1_full :
    ttFiber36StateAt 17 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix17 ++ [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 17) ttFiber36State17_in_pass1_prefix17

theorem ttFiber36State18_in_pass1_prefix18 :
    ttFiber36StateAt 18 ∈ chainClosureStep ttWord ttFiber36Prefix18 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 2 ∈
      chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix17 = ttFiber36Prefix2 ++ [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17]
      (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 2) ttFiber36State2_in_pass1_prefix2
  rw [show ttFiber36Prefix18 = ttFiber36Prefix17 ++ [ttFiber36StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 18) []
    (chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 2) hparentBefore ttFiber36ReverseSingleStep18

theorem ttFiber36State18_in_pass1_full :
    ttFiber36StateAt 18 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix18 ++ [ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix18 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 18) ttFiber36State18_in_pass1_prefix18

theorem ttFiber36State19_in_pass1_prefix19 :
    ttFiber36StateAt 19 ∈ chainClosureStep ttWord ttFiber36Prefix19 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 3 ∈
      chainClosureStep ttWord ttFiber36Prefix18 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix18 = ttFiber36Prefix3 ++ [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18]
      (chainClosureStep ttWord ttFiber36Prefix3 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 3) ttFiber36State3_in_pass1_prefix3
  rw [show ttFiber36Prefix19 = ttFiber36Prefix18 ++ [ttFiber36StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 19) []
    (chainClosureStep ttWord ttFiber36Prefix18 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 3) hparentBefore ttFiber36ReverseSingleStep19

theorem ttFiber36State19_in_pass1_full :
    ttFiber36StateAt 19 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix19 ++ [ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix19 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 19) ttFiber36State19_in_pass1_prefix19

theorem ttFiber36State20_in_pass1_prefix20 :
    ttFiber36StateAt 20 ∈ chainClosureStep ttWord ttFiber36Prefix20 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 16 ∈
      chainClosureStep ttWord ttFiber36Prefix19 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix19 = ttFiber36Prefix16 ++ [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19]
      (chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 16) ttFiber36State16_in_pass1_prefix16
  rw [show ttFiber36Prefix20 = ttFiber36Prefix19 ++ [ttFiber36StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 20) []
    (chainClosureStep ttWord ttFiber36Prefix19 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 16) hparentBefore ttFiber36ReverseSingleStep20

theorem ttFiber36State20_in_pass1_full :
    ttFiber36StateAt 20 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix20 ++ [ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix20 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 20) ttFiber36State20_in_pass1_prefix20

theorem ttFiber36State21_in_pass1_prefix21 :
    ttFiber36StateAt 21 ∈ chainClosureStep ttWord ttFiber36Prefix21 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 17 ∈
      chainClosureStep ttWord ttFiber36Prefix20 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix20 = ttFiber36Prefix17 ++ [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20]
      (chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 17) ttFiber36State17_in_pass1_prefix17
  rw [show ttFiber36Prefix21 = ttFiber36Prefix20 ++ [ttFiber36StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 21) []
    (chainClosureStep ttWord ttFiber36Prefix20 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 17) hparentBefore ttFiber36ReverseSingleStep21

theorem ttFiber36State21_in_pass1_full :
    ttFiber36StateAt 21 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix21 ++ [ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix21 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 21) ttFiber36State21_in_pass1_prefix21

theorem ttFiber36State22_in_pass1_prefix22 :
    ttFiber36StateAt 22 ∈ chainClosureStep ttWord ttFiber36Prefix22 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 6 ∈
      chainClosureStep ttWord ttFiber36Prefix21 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix21 = ttFiber36Prefix6 ++ [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21]
      (chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 6) ttFiber36State6_in_pass1_prefix6
  rw [show ttFiber36Prefix22 = ttFiber36Prefix21 ++ [ttFiber36StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 22) []
    (chainClosureStep ttWord ttFiber36Prefix21 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 6) hparentBefore ttFiber36ReverseSingleStep22

theorem ttFiber36State22_in_pass1_full :
    ttFiber36StateAt 22 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix22 ++ [ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix22 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 22) ttFiber36State22_in_pass1_prefix22

theorem ttFiber36State23_in_pass1_prefix23 :
    ttFiber36StateAt 23 ∈ chainClosureStep ttWord ttFiber36Prefix23 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 7 ∈
      chainClosureStep ttWord ttFiber36Prefix22 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix22 = ttFiber36Prefix7 ++ [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22]
      (chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 7) ttFiber36State7_in_pass1_prefix7
  rw [show ttFiber36Prefix23 = ttFiber36Prefix22 ++ [ttFiber36StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 23) []
    (chainClosureStep ttWord ttFiber36Prefix22 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 7) hparentBefore ttFiber36ReverseSingleStep23

theorem ttFiber36State23_in_pass1_full :
    ttFiber36StateAt 23 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix23 ++ [ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix23 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 23) ttFiber36State23_in_pass1_prefix23

theorem ttFiber36State24_in_pass1_prefix24 :
    ttFiber36StateAt 24 ∈ chainClosureStep ttWord ttFiber36Prefix24 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 8 ∈
      chainClosureStep ttWord ttFiber36Prefix23 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix23 = ttFiber36Prefix8 ++ [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23]
      (chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 8) ttFiber36State8_in_pass1_prefix8
  rw [show ttFiber36Prefix24 = ttFiber36Prefix23 ++ [ttFiber36StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 24) []
    (chainClosureStep ttWord ttFiber36Prefix23 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 8) hparentBefore ttFiber36ReverseSingleStep24

theorem ttFiber36State24_in_pass1_full :
    ttFiber36StateAt 24 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix24 ++ [ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix24 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 24) ttFiber36State24_in_pass1_prefix24

theorem ttFiber36State25_in_pass1_prefix25 :
    ttFiber36StateAt 25 ∈ chainClosureStep ttWord ttFiber36Prefix25 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 9 ∈
      chainClosureStep ttWord ttFiber36Prefix24 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix24 = ttFiber36Prefix9 ++ [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24]
      (chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 9) ttFiber36State9_in_pass1_prefix9
  rw [show ttFiber36Prefix25 = ttFiber36Prefix24 ++ [ttFiber36StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 25) []
    (chainClosureStep ttWord ttFiber36Prefix24 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 9) hparentBefore ttFiber36ReverseSingleStep25

theorem ttFiber36State25_in_pass1_full :
    ttFiber36StateAt 25 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix25 ++ [ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix25 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 25) ttFiber36State25_in_pass1_prefix25

theorem ttFiber36State26_in_pass1_prefix26 :
    ttFiber36StateAt 26 ∈ chainClosureStep ttWord ttFiber36Prefix26 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 10 ∈
      chainClosureStep ttWord ttFiber36Prefix25 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix25 = ttFiber36Prefix10 ++ [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25]
      (chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 10) ttFiber36State10_in_pass1_prefix10
  rw [show ttFiber36Prefix26 = ttFiber36Prefix25 ++ [ttFiber36StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 26) []
    (chainClosureStep ttWord ttFiber36Prefix25 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 10) hparentBefore ttFiber36ReverseSingleStep26

theorem ttFiber36State26_in_pass1_full :
    ttFiber36StateAt 26 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix26 ++ [ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix26 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 26) ttFiber36State26_in_pass1_prefix26

theorem ttFiber36State27_in_pass1_prefix27 :
    ttFiber36StateAt 27 ∈ chainClosureStep ttWord ttFiber36Prefix27 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 11 ∈
      chainClosureStep ttWord ttFiber36Prefix26 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix26 = ttFiber36Prefix11 ++ [ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26]
      (chainClosureStep ttWord ttFiber36Prefix11 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 11) ttFiber36State11_in_pass1_prefix11
  rw [show ttFiber36Prefix27 = ttFiber36Prefix26 ++ [ttFiber36StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 27) []
    (chainClosureStep ttWord ttFiber36Prefix26 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 11) hparentBefore ttFiber36ReverseSingleStep27

theorem ttFiber36State27_in_pass1_full :
    ttFiber36StateAt 27 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix27 ++ [ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix27 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 27) ttFiber36State27_in_pass1_prefix27

theorem ttFiber36State28_in_pass1_prefix28 :
    ttFiber36StateAt 28 ∈ chainClosureStep ttWord ttFiber36Prefix28 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 24 ∈
      chainClosureStep ttWord ttFiber36Prefix27 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix27 = ttFiber36Prefix24 ++ [ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27]
      (chainClosureStep ttWord ttFiber36Prefix24 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 24) ttFiber36State24_in_pass1_prefix24
  rw [show ttFiber36Prefix28 = ttFiber36Prefix27 ++ [ttFiber36StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 28) []
    (chainClosureStep ttWord ttFiber36Prefix27 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 24) hparentBefore ttFiber36ReverseSingleStep28

theorem ttFiber36State28_in_pass1_full :
    ttFiber36StateAt 28 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix28 ++ [ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix28 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 28) ttFiber36State28_in_pass1_prefix28

theorem ttFiber36State29_in_pass1_prefix29 :
    ttFiber36StateAt 29 ∈ chainClosureStep ttWord ttFiber36Prefix29 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 25 ∈
      chainClosureStep ttWord ttFiber36Prefix28 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix28 = ttFiber36Prefix25 ++ [ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28]
      (chainClosureStep ttWord ttFiber36Prefix25 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 25) ttFiber36State25_in_pass1_prefix25
  rw [show ttFiber36Prefix29 = ttFiber36Prefix28 ++ [ttFiber36StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 29) []
    (chainClosureStep ttWord ttFiber36Prefix28 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 25) hparentBefore ttFiber36ReverseSingleStep29

theorem ttFiber36State29_in_pass1_full :
    ttFiber36StateAt 29 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix29 ++ [ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix29 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 29) ttFiber36State29_in_pass1_prefix29

theorem ttFiber36State30_in_pass1_prefix30 :
    ttFiber36StateAt 30 ∈ chainClosureStep ttWord ttFiber36Prefix30 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 14 ∈
      chainClosureStep ttWord ttFiber36Prefix29 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix29 = ttFiber36Prefix14 ++ [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29]
      (chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 14) ttFiber36State14_in_pass1_prefix14
  rw [show ttFiber36Prefix30 = ttFiber36Prefix29 ++ [ttFiber36StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 30) []
    (chainClosureStep ttWord ttFiber36Prefix29 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 14) hparentBefore ttFiber36ReverseSingleStep30

theorem ttFiber36State30_in_pass1_full :
    ttFiber36StateAt 30 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix30 ++ [ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix30 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 30) ttFiber36State30_in_pass1_prefix30

theorem ttFiber36State31_in_pass1_prefix31 :
    ttFiber36StateAt 31 ∈ chainClosureStep ttWord ttFiber36Prefix31 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 15 ∈
      chainClosureStep ttWord ttFiber36Prefix30 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix30 = ttFiber36Prefix15 ++ [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30]
      (chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 15) ttFiber36State15_in_pass1_prefix15
  rw [show ttFiber36Prefix31 = ttFiber36Prefix30 ++ [ttFiber36StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 31) []
    (chainClosureStep ttWord ttFiber36Prefix30 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 15) hparentBefore ttFiber36ReverseSingleStep31

theorem ttFiber36State31_in_pass1_full :
    ttFiber36StateAt 31 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix31 ++ [ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix31 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 31) ttFiber36State31_in_pass1_prefix31

theorem ttFiber36State32_in_pass1_prefix32 :
    ttFiber36StateAt 32 ∈ chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 0 ∈
      chainClosureStep ttWord ttFiber36Prefix31 ([ttFiber36StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix31
      ([ttFiber36StateAt 0]) (ttFiber36StateAt 0) ttFiber36State0_in_pass0_full
  rw [show ttFiber36Prefix32 = ttFiber36Prefix31 ++ [ttFiber36StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 32) []
    (chainClosureStep ttWord ttFiber36Prefix31 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 0) hparentBefore ttFiber36ReverseSingleStep32

theorem ttFiber36State32_in_pass1_full :
    ttFiber36StateAt 32 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix32 ++ [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 32) ttFiber36State32_in_pass1_prefix32

theorem ttFiber36State33_in_pass1_prefix33 :
    ttFiber36StateAt 33 ∈ chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 1 ∈
      chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix32 = ttFiber36Prefix1 ++ [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 2, ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32]
      (chainClosureStep ttWord ttFiber36Prefix1 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 1) ttFiber36State1_in_pass1_prefix1
  rw [show ttFiber36Prefix33 = ttFiber36Prefix32 ++ [ttFiber36StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 33) []
    (chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 1) hparentBefore ttFiber36ReverseSingleStep33

theorem ttFiber36State33_in_pass1_full :
    ttFiber36StateAt 33 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix33 ++ [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 33) ttFiber36State33_in_pass1_prefix33

theorem ttFiber36State34_in_pass1_prefix34 :
    ttFiber36StateAt 34 ∈ chainClosureStep ttWord ttFiber36Prefix34 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 2 ∈
      chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix33 = ttFiber36Prefix2 ++ [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 3, ttFiber36StateAt 4, ttFiber36StateAt 5, ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33]
      (chainClosureStep ttWord ttFiber36Prefix2 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 2) ttFiber36State2_in_pass1_prefix2
  rw [show ttFiber36Prefix34 = ttFiber36Prefix33 ++ [ttFiber36StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 34) []
    (chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 2) hparentBefore ttFiber36ReverseSingleStep34

theorem ttFiber36State34_in_pass1_full :
    ttFiber36StateAt 34 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix34 ++ [ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix34 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 34) ttFiber36State34_in_pass1_prefix34

theorem ttFiber36State35_in_pass1_prefix35 :
    ttFiber36StateAt 35 ∈ chainClosureStep ttWord ttFiber36Prefix35 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 32 ∈
      chainClosureStep ttWord ttFiber36Prefix34 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix34 = ttFiber36Prefix32 ++ [ttFiber36StateAt 33, ttFiber36StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 33, ttFiber36StateAt 34]
      (chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 32) ttFiber36State32_in_pass1_prefix32
  rw [show ttFiber36Prefix35 = ttFiber36Prefix34 ++ [ttFiber36StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 35) []
    (chainClosureStep ttWord ttFiber36Prefix34 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 32) hparentBefore ttFiber36ReverseSingleStep35

theorem ttFiber36State35_in_pass1_full :
    ttFiber36StateAt 35 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix35 ++ [ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix35 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 35) ttFiber36State35_in_pass1_prefix35

theorem ttFiber36State36_in_pass1_prefix36 :
    ttFiber36StateAt 36 ∈ chainClosureStep ttWord ttFiber36Prefix36 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 32 ∈
      chainClosureStep ttWord ttFiber36Prefix35 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix35 = ttFiber36Prefix32 ++ [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35]
      (chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 32) ttFiber36State32_in_pass1_prefix32
  rw [show ttFiber36Prefix36 = ttFiber36Prefix35 ++ [ttFiber36StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 36) []
    (chainClosureStep ttWord ttFiber36Prefix35 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 32) hparentBefore ttFiber36ReverseSingleStep36

theorem ttFiber36State36_in_pass1_full :
    ttFiber36StateAt 36 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix36 ++ [ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix36 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 36) ttFiber36State36_in_pass1_prefix36

theorem ttFiber36State37_in_pass1_prefix37 :
    ttFiber36StateAt 37 ∈ chainClosureStep ttWord ttFiber36Prefix37 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 33 ∈
      chainClosureStep ttWord ttFiber36Prefix36 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix36 = ttFiber36Prefix33 ++ [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36]
      (chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 33) ttFiber36State33_in_pass1_prefix33
  rw [show ttFiber36Prefix37 = ttFiber36Prefix36 ++ [ttFiber36StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 37) []
    (chainClosureStep ttWord ttFiber36Prefix36 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 33) hparentBefore ttFiber36ReverseSingleStep37

theorem ttFiber36State37_in_pass1_full :
    ttFiber36StateAt 37 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix37 ++ [ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix37 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 37) ttFiber36State37_in_pass1_prefix37

theorem ttFiber36State38_in_pass1_prefix38 :
    ttFiber36StateAt 38 ∈ chainClosureStep ttWord ttFiber36Prefix38 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 6 ∈
      chainClosureStep ttWord ttFiber36Prefix37 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix37 = ttFiber36Prefix6 ++ [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37]
      (chainClosureStep ttWord ttFiber36Prefix6 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 6) ttFiber36State6_in_pass1_prefix6
  rw [show ttFiber36Prefix38 = ttFiber36Prefix37 ++ [ttFiber36StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 38) []
    (chainClosureStep ttWord ttFiber36Prefix37 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 6) hparentBefore ttFiber36ReverseSingleStep38

theorem ttFiber36State38_in_pass1_full :
    ttFiber36StateAt 38 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix38 ++ [ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix38 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 38) ttFiber36State38_in_pass1_prefix38

theorem ttFiber36State39_in_pass1_prefix39 :
    ttFiber36StateAt 39 ∈ chainClosureStep ttWord ttFiber36Prefix39 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 7 ∈
      chainClosureStep ttWord ttFiber36Prefix38 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix38 = ttFiber36Prefix7 ++ [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38]
      (chainClosureStep ttWord ttFiber36Prefix7 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 7) ttFiber36State7_in_pass1_prefix7
  rw [show ttFiber36Prefix39 = ttFiber36Prefix38 ++ [ttFiber36StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 39) []
    (chainClosureStep ttWord ttFiber36Prefix38 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 7) hparentBefore ttFiber36ReverseSingleStep39

theorem ttFiber36State39_in_pass1_full :
    ttFiber36StateAt 39 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix39 ++ [ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix39 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 39) ttFiber36State39_in_pass1_prefix39

theorem ttFiber36State40_in_pass1_prefix40 :
    ttFiber36StateAt 40 ∈ chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 8 ∈
      chainClosureStep ttWord ttFiber36Prefix39 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix39 = ttFiber36Prefix8 ++ [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39]
      (chainClosureStep ttWord ttFiber36Prefix8 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 8) ttFiber36State8_in_pass1_prefix8
  rw [show ttFiber36Prefix40 = ttFiber36Prefix39 ++ [ttFiber36StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 40) []
    (chainClosureStep ttWord ttFiber36Prefix39 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 8) hparentBefore ttFiber36ReverseSingleStep40

theorem ttFiber36State40_in_pass1_full :
    ttFiber36StateAt 40 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix40 ++ [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 40) ttFiber36State40_in_pass1_prefix40

theorem ttFiber36State41_in_pass1_prefix41 :
    ttFiber36StateAt 41 ∈ chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 9 ∈
      chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix40 = ttFiber36Prefix9 ++ [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40]
      (chainClosureStep ttWord ttFiber36Prefix9 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 9) ttFiber36State9_in_pass1_prefix9
  rw [show ttFiber36Prefix41 = ttFiber36Prefix40 ++ [ttFiber36StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 41) []
    (chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 9) hparentBefore ttFiber36ReverseSingleStep41

theorem ttFiber36State41_in_pass1_full :
    ttFiber36StateAt 41 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix41 ++ [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 41) ttFiber36State41_in_pass1_prefix41

theorem ttFiber36State42_in_pass1_prefix42 :
    ttFiber36StateAt 42 ∈ chainClosureStep ttWord ttFiber36Prefix42 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 10 ∈
      chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix41 = ttFiber36Prefix10 ++ [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41]
      (chainClosureStep ttWord ttFiber36Prefix10 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 10) ttFiber36State10_in_pass1_prefix10
  rw [show ttFiber36Prefix42 = ttFiber36Prefix41 ++ [ttFiber36StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 42) []
    (chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 10) hparentBefore ttFiber36ReverseSingleStep42

theorem ttFiber36State42_in_pass1_full :
    ttFiber36StateAt 42 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix42 ++ [ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix42 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 42) ttFiber36State42_in_pass1_prefix42

theorem ttFiber36State43_in_pass1_prefix43 :
    ttFiber36StateAt 43 ∈ chainClosureStep ttWord ttFiber36Prefix43 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 40 ∈
      chainClosureStep ttWord ttFiber36Prefix42 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix42 = ttFiber36Prefix40 ++ [ttFiber36StateAt 41, ttFiber36StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 41, ttFiber36StateAt 42]
      (chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 40) ttFiber36State40_in_pass1_prefix40
  rw [show ttFiber36Prefix43 = ttFiber36Prefix42 ++ [ttFiber36StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 43) []
    (chainClosureStep ttWord ttFiber36Prefix42 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 40) hparentBefore ttFiber36ReverseSingleStep43

theorem ttFiber36State43_in_pass1_full :
    ttFiber36StateAt 43 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix43 ++ [ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix43 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 43) ttFiber36State43_in_pass1_prefix43

theorem ttFiber36State44_in_pass1_prefix44 :
    ttFiber36StateAt 44 ∈ chainClosureStep ttWord ttFiber36Prefix44 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 40 ∈
      chainClosureStep ttWord ttFiber36Prefix43 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix43 = ttFiber36Prefix40 ++ [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43]
      (chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 40) ttFiber36State40_in_pass1_prefix40
  rw [show ttFiber36Prefix44 = ttFiber36Prefix43 ++ [ttFiber36StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 44) []
    (chainClosureStep ttWord ttFiber36Prefix43 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 40) hparentBefore ttFiber36ReverseSingleStep44

theorem ttFiber36State44_in_pass1_full :
    ttFiber36StateAt 44 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix44 ++ [ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix44 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 44) ttFiber36State44_in_pass1_prefix44

theorem ttFiber36State45_in_pass1_prefix45 :
    ttFiber36StateAt 45 ∈ chainClosureStep ttWord ttFiber36Prefix45 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 41 ∈
      chainClosureStep ttWord ttFiber36Prefix44 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix44 = ttFiber36Prefix41 ++ [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44]
      (chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 41) ttFiber36State41_in_pass1_prefix41
  rw [show ttFiber36Prefix45 = ttFiber36Prefix44 ++ [ttFiber36StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 45) []
    (chainClosureStep ttWord ttFiber36Prefix44 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 41) hparentBefore ttFiber36ReverseSingleStep45

theorem ttFiber36State45_in_pass1_full :
    ttFiber36StateAt 45 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix45 ++ [ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix45 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 45) ttFiber36State45_in_pass1_prefix45

theorem ttFiber36State46_in_pass1_prefix46 :
    ttFiber36StateAt 46 ∈ chainClosureStep ttWord ttFiber36Prefix46 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 14 ∈
      chainClosureStep ttWord ttFiber36Prefix45 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix45 = ttFiber36Prefix14 ++ [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45]
      (chainClosureStep ttWord ttFiber36Prefix14 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 14) ttFiber36State14_in_pass1_prefix14
  rw [show ttFiber36Prefix46 = ttFiber36Prefix45 ++ [ttFiber36StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 46) []
    (chainClosureStep ttWord ttFiber36Prefix45 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 14) hparentBefore ttFiber36ReverseSingleStep46

theorem ttFiber36State46_in_pass1_full :
    ttFiber36StateAt 46 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix46 ++ [ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix46 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 46) ttFiber36State46_in_pass1_prefix46

theorem ttFiber36State47_in_pass1_prefix47 :
    ttFiber36StateAt 47 ∈ chainClosureStep ttWord ttFiber36Prefix47 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 15 ∈
      chainClosureStep ttWord ttFiber36Prefix46 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix46 = ttFiber36Prefix15 ++ [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46]
      (chainClosureStep ttWord ttFiber36Prefix15 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 15) ttFiber36State15_in_pass1_prefix15
  rw [show ttFiber36Prefix47 = ttFiber36Prefix46 ++ [ttFiber36StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 47) []
    (chainClosureStep ttWord ttFiber36Prefix46 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 15) hparentBefore ttFiber36ReverseSingleStep47

theorem ttFiber36State47_in_pass1_full :
    ttFiber36StateAt 47 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix47 ++ [ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix47 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 47) ttFiber36State47_in_pass1_prefix47

theorem ttFiber36State48_in_pass1_prefix48 :
    ttFiber36StateAt 48 ∈ chainClosureStep ttWord ttFiber36Prefix48 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 16 ∈
      chainClosureStep ttWord ttFiber36Prefix47 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix47 = ttFiber36Prefix16 ++ [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47]
      (chainClosureStep ttWord ttFiber36Prefix16 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 16) ttFiber36State16_in_pass1_prefix16
  rw [show ttFiber36Prefix48 = ttFiber36Prefix47 ++ [ttFiber36StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 48) []
    (chainClosureStep ttWord ttFiber36Prefix47 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 16) hparentBefore ttFiber36ReverseSingleStep48

theorem ttFiber36State48_in_pass1_full :
    ttFiber36StateAt 48 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix48 ++ [ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix48 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 48) ttFiber36State48_in_pass1_prefix48

theorem ttFiber36State49_in_pass1_prefix49 :
    ttFiber36StateAt 49 ∈ chainClosureStep ttWord ttFiber36Prefix49 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 17 ∈
      chainClosureStep ttWord ttFiber36Prefix48 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix48 = ttFiber36Prefix17 ++ [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48]
      (chainClosureStep ttWord ttFiber36Prefix17 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 17) ttFiber36State17_in_pass1_prefix17
  rw [show ttFiber36Prefix49 = ttFiber36Prefix48 ++ [ttFiber36StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 49) []
    (chainClosureStep ttWord ttFiber36Prefix48 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 17) hparentBefore ttFiber36ReverseSingleStep49

theorem ttFiber36State49_in_pass1_full :
    ttFiber36StateAt 49 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix49 ++ [ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix49 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 49) ttFiber36State49_in_pass1_prefix49

theorem ttFiber36State50_in_pass1_prefix50 :
    ttFiber36StateAt 50 ∈ chainClosureStep ttWord ttFiber36Prefix50 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 18 ∈
      chainClosureStep ttWord ttFiber36Prefix49 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix49 = ttFiber36Prefix18 ++ [ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49]
      (chainClosureStep ttWord ttFiber36Prefix18 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 18) ttFiber36State18_in_pass1_prefix18
  rw [show ttFiber36Prefix50 = ttFiber36Prefix49 ++ [ttFiber36StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 50) []
    (chainClosureStep ttWord ttFiber36Prefix49 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 18) hparentBefore ttFiber36ReverseSingleStep50

theorem ttFiber36State50_in_pass1_full :
    ttFiber36StateAt 50 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix50 ++ [ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix50 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 50) ttFiber36State50_in_pass1_prefix50

theorem ttFiber36State51_in_pass1_prefix51 :
    ttFiber36StateAt 51 ∈ chainClosureStep ttWord ttFiber36Prefix51 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 19 ∈
      chainClosureStep ttWord ttFiber36Prefix50 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix50 = ttFiber36Prefix19 ++ [ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50]
      (chainClosureStep ttWord ttFiber36Prefix19 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 19) ttFiber36State19_in_pass1_prefix19
  rw [show ttFiber36Prefix51 = ttFiber36Prefix50 ++ [ttFiber36StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 51) []
    (chainClosureStep ttWord ttFiber36Prefix50 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 19) hparentBefore ttFiber36ReverseSingleStep51

theorem ttFiber36State51_in_pass1_full :
    ttFiber36StateAt 51 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix51 ++ [ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix51 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 51) ttFiber36State51_in_pass1_prefix51

theorem ttFiber36State52_in_pass1_prefix52 :
    ttFiber36StateAt 52 ∈ chainClosureStep ttWord ttFiber36Prefix52 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 40 ∈
      chainClosureStep ttWord ttFiber36Prefix51 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix51 = ttFiber36Prefix40 ++ [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51]
      (chainClosureStep ttWord ttFiber36Prefix40 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 40) ttFiber36State40_in_pass1_prefix40
  rw [show ttFiber36Prefix52 = ttFiber36Prefix51 ++ [ttFiber36StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 52) []
    (chainClosureStep ttWord ttFiber36Prefix51 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 40) hparentBefore ttFiber36ReverseSingleStep52

theorem ttFiber36State52_in_pass1_full :
    ttFiber36StateAt 52 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix52 ++ [ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix52 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 52) ttFiber36State52_in_pass1_prefix52

theorem ttFiber36State53_in_pass1_prefix53 :
    ttFiber36StateAt 53 ∈ chainClosureStep ttWord ttFiber36Prefix53 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 41 ∈
      chainClosureStep ttWord ttFiber36Prefix52 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix52 = ttFiber36Prefix41 ++ [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52]
      (chainClosureStep ttWord ttFiber36Prefix41 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 41) ttFiber36State41_in_pass1_prefix41
  rw [show ttFiber36Prefix53 = ttFiber36Prefix52 ++ [ttFiber36StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 53) []
    (chainClosureStep ttWord ttFiber36Prefix52 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 41) hparentBefore ttFiber36ReverseSingleStep53

theorem ttFiber36State53_in_pass1_full :
    ttFiber36StateAt 53 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix53 ++ [ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix53 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 53) ttFiber36State53_in_pass1_prefix53

theorem ttFiber36State54_in_pass1_prefix54 :
    ttFiber36StateAt 54 ∈ chainClosureStep ttWord ttFiber36Prefix54 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 22 ∈
      chainClosureStep ttWord ttFiber36Prefix53 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix53 = ttFiber36Prefix22 ++ [ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53]
      (chainClosureStep ttWord ttFiber36Prefix22 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 22) ttFiber36State22_in_pass1_prefix22
  rw [show ttFiber36Prefix54 = ttFiber36Prefix53 ++ [ttFiber36StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 54) []
    (chainClosureStep ttWord ttFiber36Prefix53 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 22) hparentBefore ttFiber36ReverseSingleStep54

theorem ttFiber36State54_in_pass1_full :
    ttFiber36StateAt 54 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix54 ++ [ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix54 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 54) ttFiber36State54_in_pass1_prefix54

theorem ttFiber36State55_in_pass1_prefix55 :
    ttFiber36StateAt 55 ∈ chainClosureStep ttWord ttFiber36Prefix55 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 23 ∈
      chainClosureStep ttWord ttFiber36Prefix54 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix54 = ttFiber36Prefix23 ++ [ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54]
      (chainClosureStep ttWord ttFiber36Prefix23 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 23) ttFiber36State23_in_pass1_prefix23
  rw [show ttFiber36Prefix55 = ttFiber36Prefix54 ++ [ttFiber36StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 55) []
    (chainClosureStep ttWord ttFiber36Prefix54 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 23) hparentBefore ttFiber36ReverseSingleStep55

theorem ttFiber36State55_in_pass1_full :
    ttFiber36StateAt 55 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix55 ++ [ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix55 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 55) ttFiber36State55_in_pass1_prefix55

theorem ttFiber36State56_in_pass1_prefix56 :
    ttFiber36StateAt 56 ∈ chainClosureStep ttWord ttFiber36Prefix56 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 39 ∈
      chainClosureStep ttWord ttFiber36Prefix55 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix55 = ttFiber36Prefix39 ++ [ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55]
      (chainClosureStep ttWord ttFiber36Prefix39 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 39) ttFiber36State39_in_pass1_prefix39
  rw [show ttFiber36Prefix56 = ttFiber36Prefix55 ++ [ttFiber36StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 56) []
    (chainClosureStep ttWord ttFiber36Prefix55 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 39) hparentBefore ttFiber36ReverseSingleStep56

theorem ttFiber36State56_in_pass1_full :
    ttFiber36StateAt 56 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix56 ++ [ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix56 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 56) ttFiber36State56_in_pass1_prefix56

theorem ttFiber36State57_in_pass1_prefix57 :
    ttFiber36StateAt 57 ∈ chainClosureStep ttWord ttFiber36Prefix57 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 38 ∈
      chainClosureStep ttWord ttFiber36Prefix56 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix56 = ttFiber36Prefix38 ++ [ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56]
      (chainClosureStep ttWord ttFiber36Prefix38 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 38) ttFiber36State38_in_pass1_prefix38
  rw [show ttFiber36Prefix57 = ttFiber36Prefix56 ++ [ttFiber36StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 57) []
    (chainClosureStep ttWord ttFiber36Prefix56 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 38) hparentBefore ttFiber36ReverseSingleStep57

theorem ttFiber36State57_in_pass1_full :
    ttFiber36StateAt 57 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix57 ++ [ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix57 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 57) ttFiber36State57_in_pass1_prefix57

theorem ttFiber36State58_in_pass1_prefix58 :
    ttFiber36StateAt 58 ∈ chainClosureStep ttWord ttFiber36Prefix58 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 36 ∈
      chainClosureStep ttWord ttFiber36Prefix57 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix57 = ttFiber36Prefix36 ++ [ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57]
      (chainClosureStep ttWord ttFiber36Prefix36 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 36) ttFiber36State36_in_pass1_prefix36
  rw [show ttFiber36Prefix58 = ttFiber36Prefix57 ++ [ttFiber36StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 58) []
    (chainClosureStep ttWord ttFiber36Prefix57 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 36) hparentBefore ttFiber36ReverseSingleStep58

theorem ttFiber36State58_in_pass1_full :
    ttFiber36StateAt 58 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix58 ++ [ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix58 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 58) ttFiber36State58_in_pass1_prefix58

theorem ttFiber36State59_in_pass1_prefix59 :
    ttFiber36StateAt 59 ∈ chainClosureStep ttWord ttFiber36Prefix59 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 37 ∈
      chainClosureStep ttWord ttFiber36Prefix58 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix58 = ttFiber36Prefix37 ++ [ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58]
      (chainClosureStep ttWord ttFiber36Prefix37 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 37) ttFiber36State37_in_pass1_prefix37
  rw [show ttFiber36Prefix59 = ttFiber36Prefix58 ++ [ttFiber36StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 59) []
    (chainClosureStep ttWord ttFiber36Prefix58 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 37) hparentBefore ttFiber36ReverseSingleStep59

theorem ttFiber36State59_in_pass1_full :
    ttFiber36StateAt 59 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix59 ++ [ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix59 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 59) ttFiber36State59_in_pass1_prefix59

theorem ttFiber36State60_in_pass1_prefix60 :
    ttFiber36StateAt 60 ∈ chainClosureStep ttWord ttFiber36Prefix60 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 32 ∈
      chainClosureStep ttWord ttFiber36Prefix59 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix59 = ttFiber36Prefix32 ++ [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59]
      (chainClosureStep ttWord ttFiber36Prefix32 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 32) ttFiber36State32_in_pass1_prefix32
  rw [show ttFiber36Prefix60 = ttFiber36Prefix59 ++ [ttFiber36StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 60) []
    (chainClosureStep ttWord ttFiber36Prefix59 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 32) hparentBefore ttFiber36ReverseSingleStep60

theorem ttFiber36State60_in_pass1_full :
    ttFiber36StateAt 60 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix60 ++ [ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix60 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 60) ttFiber36State60_in_pass1_prefix60

theorem ttFiber36State61_in_pass1_prefix61 :
    ttFiber36StateAt 61 ∈ chainClosureStep ttWord ttFiber36Prefix61 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 33 ∈
      chainClosureStep ttWord ttFiber36Prefix60 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix60 = ttFiber36Prefix33 ++ [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60]
      (chainClosureStep ttWord ttFiber36Prefix33 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 33) ttFiber36State33_in_pass1_prefix33
  rw [show ttFiber36Prefix61 = ttFiber36Prefix60 ++ [ttFiber36StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 61) []
    (chainClosureStep ttWord ttFiber36Prefix60 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 33) hparentBefore ttFiber36ReverseSingleStep61

theorem ttFiber36State61_in_pass1_full :
    ttFiber36StateAt 61 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix61 ++ [ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix61 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 61) ttFiber36State61_in_pass1_prefix61

theorem ttFiber36State62_in_pass1_prefix62 :
    ttFiber36StateAt 62 ∈ chainClosureStep ttWord ttFiber36Prefix62 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 34 ∈
      chainClosureStep ttWord ttFiber36Prefix61 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix61 = ttFiber36Prefix34 ++ [ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61]
      (chainClosureStep ttWord ttFiber36Prefix34 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 34) ttFiber36State34_in_pass1_prefix34
  rw [show ttFiber36Prefix62 = ttFiber36Prefix61 ++ [ttFiber36StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 62) []
    (chainClosureStep ttWord ttFiber36Prefix61 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 34) hparentBefore ttFiber36ReverseSingleStep62

theorem ttFiber36State62_in_pass1_full :
    ttFiber36StateAt 62 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix62 ++ [ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix62 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 62) ttFiber36State62_in_pass1_prefix62

theorem ttFiber36State63_in_pass1_prefix63 :
    ttFiber36StateAt 63 ∈ chainClosureStep ttWord ttFiber36Prefix63 ([ttFiber36StateAt 0]) := by
  have hparentBefore : ttFiber36StateAt 35 ∈
      chainClosureStep ttWord ttFiber36Prefix62 ([ttFiber36StateAt 0]) := by
    rw [show ttFiber36Prefix62 = ttFiber36Prefix35 ++ [ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62]
      (chainClosureStep ttWord ttFiber36Prefix35 ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 35) ttFiber36State35_in_pass1_prefix35
  rw [show ttFiber36Prefix63 = ttFiber36Prefix62 ++ [ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 63) []
    (chainClosureStep ttWord ttFiber36Prefix62 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 35) hparentBefore ttFiber36ReverseSingleStep63

theorem ttFiber36State63_in_pass1_full :
    ttFiber36StateAt 63 ∈ chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber36Prefix63 ([ttFiber36StateAt 0]))
    (ttFiber36StateAt 63) ttFiber36State63_in_pass1_prefix63

theorem ttFiber36State5_in_pass2_prefix5 :
    ttFiber36StateAt 5 ∈ chainClosureStep ttWord ttFiber36Prefix5 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
  have hparentBefore : ttFiber36StateAt 7 ∈
      chainClosureStep ttWord ttFiber36Prefix4 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber36Prefix4
      (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0]))
      (ttFiber36StateAt 7) ttFiber36State7_in_pass1_full
  rw [show ttFiber36Prefix5 = ttFiber36Prefix4 ++ [ttFiber36StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 5) []
    (chainClosureStep ttWord ttFiber36Prefix4 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])))
    (ttFiber36StateAt 7) hparentBefore ttFiber36ReverseSingleStep5

theorem ttFiber36State5_in_pass2_full :
    ttFiber36StateAt 5 ∈ chainClosureStep ttWord ttFiber36DirectStates (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix5 ++ [ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12, ttFiber36StateAt 13, ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix5 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])))
    (ttFiber36StateAt 5) ttFiber36State5_in_pass2_prefix5

theorem ttFiber36State13_in_pass2_prefix13 :
    ttFiber36StateAt 13 ∈ chainClosureStep ttWord ttFiber36Prefix13 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
  have hparentBefore : ttFiber36StateAt 5 ∈
      chainClosureStep ttWord ttFiber36Prefix12 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
    rw [show ttFiber36Prefix12 = ttFiber36Prefix5 ++ [ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 6, ttFiber36StateAt 7, ttFiber36StateAt 8, ttFiber36StateAt 9, ttFiber36StateAt 10, ttFiber36StateAt 11, ttFiber36StateAt 12]
      (chainClosureStep ttWord ttFiber36Prefix5 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])))
      (ttFiber36StateAt 5) ttFiber36State5_in_pass2_prefix5
  rw [show ttFiber36Prefix13 = ttFiber36Prefix12 ++ [ttFiber36StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber36StateAt 13) []
    (chainClosureStep ttWord ttFiber36Prefix12 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])))
    (ttFiber36StateAt 5) hparentBefore ttFiber36ReverseSingleStep13

theorem ttFiber36State13_in_pass2_full :
    ttFiber36StateAt 13 ∈ chainClosureStep ttWord ttFiber36DirectStates (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])) := by
  rw [show ttFiber36DirectStates = ttFiber36Prefix13 ++ [ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber36StateAt 14, ttFiber36StateAt 15, ttFiber36StateAt 16, ttFiber36StateAt 17, ttFiber36StateAt 18, ttFiber36StateAt 19, ttFiber36StateAt 20, ttFiber36StateAt 21, ttFiber36StateAt 22, ttFiber36StateAt 23, ttFiber36StateAt 24, ttFiber36StateAt 25, ttFiber36StateAt 26, ttFiber36StateAt 27, ttFiber36StateAt 28, ttFiber36StateAt 29, ttFiber36StateAt 30, ttFiber36StateAt 31, ttFiber36StateAt 32, ttFiber36StateAt 33, ttFiber36StateAt 34, ttFiber36StateAt 35, ttFiber36StateAt 36, ttFiber36StateAt 37, ttFiber36StateAt 38, ttFiber36StateAt 39, ttFiber36StateAt 40, ttFiber36StateAt 41, ttFiber36StateAt 42, ttFiber36StateAt 43, ttFiber36StateAt 44, ttFiber36StateAt 45, ttFiber36StateAt 46, ttFiber36StateAt 47, ttFiber36StateAt 48, ttFiber36StateAt 49, ttFiber36StateAt 50, ttFiber36StateAt 51, ttFiber36StateAt 52, ttFiber36StateAt 53, ttFiber36StateAt 54, ttFiber36StateAt 55, ttFiber36StateAt 56, ttFiber36StateAt 57, ttFiber36StateAt 58, ttFiber36StateAt 59, ttFiber36StateAt 60, ttFiber36StateAt 61, ttFiber36StateAt 62, ttFiber36StateAt 63]
    (chainClosureStep ttWord ttFiber36Prefix13 (chainClosureStep ttWord ttFiber36DirectStates ([ttFiber36StateAt 0])))
    (ttFiber36StateAt 13) ttFiber36State13_in_pass2_prefix13

theorem ttFiber36State0_in_close :
    ttFiber36StateAt 0 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber36DirectStates ttFiber36DirectStates.length
    [ttFiber36StateAt 0] (ttFiber36StateAt 0) (by simp)

theorem ttFiber36State1_in_close :
    ttFiber36StateAt 1 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 1 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 1) ttFiber36State1_in_pass1_full

theorem ttFiber36State2_in_close :
    ttFiber36StateAt 2 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 2 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 2) ttFiber36State2_in_pass1_full

theorem ttFiber36State3_in_close :
    ttFiber36StateAt 3 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 3 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 3) ttFiber36State3_in_pass1_full

theorem ttFiber36State4_in_close :
    ttFiber36StateAt 4 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 4 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 4) ttFiber36State4_in_pass1_full

theorem ttFiber36State5_in_close :
    ttFiber36StateAt 5 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 5 ∈ closeChainFiber ttWord ttFiber36DirectStates (62 + 2)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber36DirectStates 62
    [ttFiber36StateAt 0] (ttFiber36StateAt 5) ttFiber36FirstPassGrows
    ttFiber36State5_in_pass2_full

theorem ttFiber36State6_in_close :
    ttFiber36StateAt 6 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 6 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 6) ttFiber36State6_in_pass1_full

theorem ttFiber36State7_in_close :
    ttFiber36StateAt 7 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 7 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 7) ttFiber36State7_in_pass1_full

theorem ttFiber36State8_in_close :
    ttFiber36StateAt 8 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 8 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 8) ttFiber36State8_in_pass1_full

theorem ttFiber36State9_in_close :
    ttFiber36StateAt 9 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 9 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 9) ttFiber36State9_in_pass1_full

theorem ttFiber36State10_in_close :
    ttFiber36StateAt 10 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 10 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 10) ttFiber36State10_in_pass1_full

theorem ttFiber36State11_in_close :
    ttFiber36StateAt 11 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 11 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 11) ttFiber36State11_in_pass1_full

theorem ttFiber36State12_in_close :
    ttFiber36StateAt 12 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 12 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 12) ttFiber36State12_in_pass1_full

theorem ttFiber36State13_in_close :
    ttFiber36StateAt 13 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 13 ∈ closeChainFiber ttWord ttFiber36DirectStates (62 + 2)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber36DirectStates 62
    [ttFiber36StateAt 0] (ttFiber36StateAt 13) ttFiber36FirstPassGrows
    ttFiber36State13_in_pass2_full

theorem ttFiber36State14_in_close :
    ttFiber36StateAt 14 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 14 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 14) ttFiber36State14_in_pass1_full

theorem ttFiber36State15_in_close :
    ttFiber36StateAt 15 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 15 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 15) ttFiber36State15_in_pass1_full

theorem ttFiber36State16_in_close :
    ttFiber36StateAt 16 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 16 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 16) ttFiber36State16_in_pass1_full

theorem ttFiber36State17_in_close :
    ttFiber36StateAt 17 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 17 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 17) ttFiber36State17_in_pass1_full

theorem ttFiber36State18_in_close :
    ttFiber36StateAt 18 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 18 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 18) ttFiber36State18_in_pass1_full

theorem ttFiber36State19_in_close :
    ttFiber36StateAt 19 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 19 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 19) ttFiber36State19_in_pass1_full

theorem ttFiber36State20_in_close :
    ttFiber36StateAt 20 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 20 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 20) ttFiber36State20_in_pass1_full

theorem ttFiber36State21_in_close :
    ttFiber36StateAt 21 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 21 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 21) ttFiber36State21_in_pass1_full

theorem ttFiber36State22_in_close :
    ttFiber36StateAt 22 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 22 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 22) ttFiber36State22_in_pass1_full

theorem ttFiber36State23_in_close :
    ttFiber36StateAt 23 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 23 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 23) ttFiber36State23_in_pass1_full

theorem ttFiber36State24_in_close :
    ttFiber36StateAt 24 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 24 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 24) ttFiber36State24_in_pass1_full

theorem ttFiber36State25_in_close :
    ttFiber36StateAt 25 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 25 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 25) ttFiber36State25_in_pass1_full

theorem ttFiber36State26_in_close :
    ttFiber36StateAt 26 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 26 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 26) ttFiber36State26_in_pass1_full

theorem ttFiber36State27_in_close :
    ttFiber36StateAt 27 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 27 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 27) ttFiber36State27_in_pass1_full

theorem ttFiber36State28_in_close :
    ttFiber36StateAt 28 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 28 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 28) ttFiber36State28_in_pass1_full

theorem ttFiber36State29_in_close :
    ttFiber36StateAt 29 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 29 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 29) ttFiber36State29_in_pass1_full

theorem ttFiber36State30_in_close :
    ttFiber36StateAt 30 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 30 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 30) ttFiber36State30_in_pass1_full

theorem ttFiber36State31_in_close :
    ttFiber36StateAt 31 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 31 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 31) ttFiber36State31_in_pass1_full

theorem ttFiber36State32_in_close :
    ttFiber36StateAt 32 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 32 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 32) ttFiber36State32_in_pass1_full

theorem ttFiber36State33_in_close :
    ttFiber36StateAt 33 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 33 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 33) ttFiber36State33_in_pass1_full

theorem ttFiber36State34_in_close :
    ttFiber36StateAt 34 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 34 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 34) ttFiber36State34_in_pass1_full

theorem ttFiber36State35_in_close :
    ttFiber36StateAt 35 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 35 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 35) ttFiber36State35_in_pass1_full

theorem ttFiber36State36_in_close :
    ttFiber36StateAt 36 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 36 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 36) ttFiber36State36_in_pass1_full

theorem ttFiber36State37_in_close :
    ttFiber36StateAt 37 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 37 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 37) ttFiber36State37_in_pass1_full

theorem ttFiber36State38_in_close :
    ttFiber36StateAt 38 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 38 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 38) ttFiber36State38_in_pass1_full

theorem ttFiber36State39_in_close :
    ttFiber36StateAt 39 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 39 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 39) ttFiber36State39_in_pass1_full

theorem ttFiber36State40_in_close :
    ttFiber36StateAt 40 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 40 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 40) ttFiber36State40_in_pass1_full

theorem ttFiber36State41_in_close :
    ttFiber36StateAt 41 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 41 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 41) ttFiber36State41_in_pass1_full

theorem ttFiber36State42_in_close :
    ttFiber36StateAt 42 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 42 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 42) ttFiber36State42_in_pass1_full

theorem ttFiber36State43_in_close :
    ttFiber36StateAt 43 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 43 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 43) ttFiber36State43_in_pass1_full

theorem ttFiber36State44_in_close :
    ttFiber36StateAt 44 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 44 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 44) ttFiber36State44_in_pass1_full

theorem ttFiber36State45_in_close :
    ttFiber36StateAt 45 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 45 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 45) ttFiber36State45_in_pass1_full

theorem ttFiber36State46_in_close :
    ttFiber36StateAt 46 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 46 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 46) ttFiber36State46_in_pass1_full

theorem ttFiber36State47_in_close :
    ttFiber36StateAt 47 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 47 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 47) ttFiber36State47_in_pass1_full

theorem ttFiber36State48_in_close :
    ttFiber36StateAt 48 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 48 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 48) ttFiber36State48_in_pass1_full

theorem ttFiber36State49_in_close :
    ttFiber36StateAt 49 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 49 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 49) ttFiber36State49_in_pass1_full

theorem ttFiber36State50_in_close :
    ttFiber36StateAt 50 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 50 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 50) ttFiber36State50_in_pass1_full

theorem ttFiber36State51_in_close :
    ttFiber36StateAt 51 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 51 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 51) ttFiber36State51_in_pass1_full

theorem ttFiber36State52_in_close :
    ttFiber36StateAt 52 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 52 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 52) ttFiber36State52_in_pass1_full

theorem ttFiber36State53_in_close :
    ttFiber36StateAt 53 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 53 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 53) ttFiber36State53_in_pass1_full

theorem ttFiber36State54_in_close :
    ttFiber36StateAt 54 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 54 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 54) ttFiber36State54_in_pass1_full

theorem ttFiber36State55_in_close :
    ttFiber36StateAt 55 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 55 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 55) ttFiber36State55_in_pass1_full

theorem ttFiber36State56_in_close :
    ttFiber36StateAt 56 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 56 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 56) ttFiber36State56_in_pass1_full

theorem ttFiber36State57_in_close :
    ttFiber36StateAt 57 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 57 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 57) ttFiber36State57_in_pass1_full

theorem ttFiber36State58_in_close :
    ttFiber36StateAt 58 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 58 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 58) ttFiber36State58_in_pass1_full

theorem ttFiber36State59_in_close :
    ttFiber36StateAt 59 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 59 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 59) ttFiber36State59_in_pass1_full

theorem ttFiber36State60_in_close :
    ttFiber36StateAt 60 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 60 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 60) ttFiber36State60_in_pass1_full

theorem ttFiber36State61_in_close :
    ttFiber36StateAt 61 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 61 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 61) ttFiber36State61_in_pass1_full

theorem ttFiber36State62_in_close :
    ttFiber36StateAt 62 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 62 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 62) ttFiber36State62_in_pass1_full

theorem ttFiber36State63_in_close :
    ttFiber36StateAt 63 ∈
      closeChainFiber ttWord ttFiber36DirectStates ttFiber36DirectStates.length
        [ttFiber36StateAt 0] := by
  change ttFiber36StateAt 63 ∈ closeChainFiber ttWord ttFiber36DirectStates (63 + 1)
    [ttFiber36StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber36DirectStates 63
    [ttFiber36StateAt 0] (ttFiber36StateAt 63) ttFiber36State63_in_pass1_full

theorem ttFiber36DirectConnected :
    chainFiberConnected ttWord ttFiber36DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber36DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber36State0_in_close
  · subst state
    exact ttFiber36State1_in_close
  · subst state
    exact ttFiber36State2_in_close
  · subst state
    exact ttFiber36State3_in_close
  · subst state
    exact ttFiber36State4_in_close
  · subst state
    exact ttFiber36State5_in_close
  · subst state
    exact ttFiber36State6_in_close
  · subst state
    exact ttFiber36State7_in_close
  · subst state
    exact ttFiber36State8_in_close
  · subst state
    exact ttFiber36State9_in_close
  · subst state
    exact ttFiber36State10_in_close
  · subst state
    exact ttFiber36State11_in_close
  · subst state
    exact ttFiber36State12_in_close
  · subst state
    exact ttFiber36State13_in_close
  · subst state
    exact ttFiber36State14_in_close
  · subst state
    exact ttFiber36State15_in_close
  · subst state
    exact ttFiber36State16_in_close
  · subst state
    exact ttFiber36State17_in_close
  · subst state
    exact ttFiber36State18_in_close
  · subst state
    exact ttFiber36State19_in_close
  · subst state
    exact ttFiber36State20_in_close
  · subst state
    exact ttFiber36State21_in_close
  · subst state
    exact ttFiber36State22_in_close
  · subst state
    exact ttFiber36State23_in_close
  · subst state
    exact ttFiber36State24_in_close
  · subst state
    exact ttFiber36State25_in_close
  · subst state
    exact ttFiber36State26_in_close
  · subst state
    exact ttFiber36State27_in_close
  · subst state
    exact ttFiber36State28_in_close
  · subst state
    exact ttFiber36State29_in_close
  · subst state
    exact ttFiber36State30_in_close
  · subst state
    exact ttFiber36State31_in_close
  · subst state
    exact ttFiber36State32_in_close
  · subst state
    exact ttFiber36State33_in_close
  · subst state
    exact ttFiber36State34_in_close
  · subst state
    exact ttFiber36State35_in_close
  · subst state
    exact ttFiber36State36_in_close
  · subst state
    exact ttFiber36State37_in_close
  · subst state
    exact ttFiber36State38_in_close
  · subst state
    exact ttFiber36State39_in_close
  · subst state
    exact ttFiber36State40_in_close
  · subst state
    exact ttFiber36State41_in_close
  · subst state
    exact ttFiber36State42_in_close
  · subst state
    exact ttFiber36State43_in_close
  · subst state
    exact ttFiber36State44_in_close
  · subst state
    exact ttFiber36State45_in_close
  · subst state
    exact ttFiber36State46_in_close
  · subst state
    exact ttFiber36State47_in_close
  · subst state
    exact ttFiber36State48_in_close
  · subst state
    exact ttFiber36State49_in_close
  · subst state
    exact ttFiber36State50_in_close
  · subst state
    exact ttFiber36State51_in_close
  · subst state
    exact ttFiber36State52_in_close
  · subst state
    exact ttFiber36State53_in_close
  · subst state
    exact ttFiber36State54_in_close
  · subst state
    exact ttFiber36State55_in_close
  · subst state
    exact ttFiber36State56_in_close
  · subst state
    exact ttFiber36State57_in_close
  · subst state
    exact ttFiber36State58_in_close
  · subst state
    exact ttFiber36State59_in_close
  · subst state
    exact ttFiber36State60_in_close
  · subst state
    exact ttFiber36State61_in_close
  · subst state
    exact ttFiber36State62_in_close
  · subst state
    exact ttFiber36State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
