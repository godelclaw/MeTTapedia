import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber72

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber72StateAt (i : Nat) : List TauState :=
  directStates (ttFiber72RowAt i).sourceLeft (ttFiber72RowAt i).sourceRight

def ttFiber72DirectStates : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]

def ttFiber72Prefix0 : List (List TauState) :=
  [ttFiber72StateAt 0]

def ttFiber72Prefix1 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1]

def ttFiber72Prefix2 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2]

def ttFiber72Prefix3 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3]

def ttFiber72Prefix4 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4]

def ttFiber72Prefix5 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5]

def ttFiber72Prefix6 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6]

def ttFiber72Prefix7 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7]

def ttFiber72Prefix8 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8]

def ttFiber72Prefix9 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9]

def ttFiber72Prefix10 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10]

def ttFiber72Prefix11 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11]

def ttFiber72Prefix12 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12]

def ttFiber72Prefix13 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13]

def ttFiber72Prefix14 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14]

def ttFiber72Prefix15 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15]

def ttFiber72Prefix16 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16]

def ttFiber72Prefix17 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17]

def ttFiber72Prefix18 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18]

def ttFiber72Prefix19 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19]

def ttFiber72Prefix20 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20]

def ttFiber72Prefix21 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21]

def ttFiber72Prefix22 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22]

def ttFiber72Prefix23 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23]

def ttFiber72Prefix24 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24]

def ttFiber72Prefix25 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25]

def ttFiber72Prefix26 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26]

def ttFiber72Prefix27 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27]

def ttFiber72Prefix28 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28]

def ttFiber72Prefix29 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29]

def ttFiber72Prefix30 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30]

def ttFiber72Prefix31 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31]

def ttFiber72Prefix32 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32]

def ttFiber72Prefix33 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33]

def ttFiber72Prefix34 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34]

def ttFiber72Prefix35 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35]

def ttFiber72Prefix36 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36]

def ttFiber72Prefix37 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37]

def ttFiber72Prefix38 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38]

def ttFiber72Prefix39 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39]

def ttFiber72Prefix40 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40]

def ttFiber72Prefix41 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41]

def ttFiber72Prefix42 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42]

def ttFiber72Prefix43 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43]

def ttFiber72Prefix44 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44]

def ttFiber72Prefix45 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45]

def ttFiber72Prefix46 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46]

def ttFiber72Prefix47 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47]

def ttFiber72Prefix48 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48]

def ttFiber72Prefix49 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49]

def ttFiber72Prefix50 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50]

def ttFiber72Prefix51 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51]

def ttFiber72Prefix52 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52]

def ttFiber72Prefix53 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53]

def ttFiber72Prefix54 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54]

def ttFiber72Prefix55 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55]

def ttFiber72Prefix56 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56]

def ttFiber72Prefix57 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57]

def ttFiber72Prefix58 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58]

def ttFiber72Prefix59 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59]

def ttFiber72Prefix60 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60]

def ttFiber72Prefix61 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61]

def ttFiber72Prefix62 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62]

def ttFiber72Prefix63 : List (List TauState) :=
  [ttFiber72StateAt 0, ttFiber72StateAt 1, ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]

theorem ttFiber72ReverseRow_1_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk0] at h
  exact h.2

theorem ttFiber72ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 1)
      (ttFiber72RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 1) (by decide) ttFiber72ReverseRow_1_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_2_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk1] at h
  exact h.1

theorem ttFiber72ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 2)
      (ttFiber72RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 2) (by decide) ttFiber72ReverseRow_2_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_3_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk1] at h
  exact h.2

theorem ttFiber72ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 3)
      (ttFiber72RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 3) (by decide) ttFiber72ReverseRow_3_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_4_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk2] at h
  exact h.1

theorem ttFiber72ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 4)
      (ttFiber72RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 4) (by decide) ttFiber72ReverseRow_4_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_5_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk2] at h
  exact h.2

theorem ttFiber72ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 5)
      (ttFiber72RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 5) (by decide) ttFiber72ReverseRow_5_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_6_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk3] at h
  exact h.1

theorem ttFiber72ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 6)
      (ttFiber72RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 6) (by decide) ttFiber72ReverseRow_6_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_7_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk3] at h
  exact h.2

theorem ttFiber72ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 7)
      (ttFiber72RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 7) (by decide) ttFiber72ReverseRow_7_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_8_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk4] at h
  exact h.1

theorem ttFiber72ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 8)
      (ttFiber72RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 8) (by decide) ttFiber72ReverseRow_8_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_9_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk4] at h
  exact h.2

theorem ttFiber72ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 9)
      (ttFiber72RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 9) (by decide) ttFiber72ReverseRow_9_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_10_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk5] at h
  exact h.1

theorem ttFiber72ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 10)
      (ttFiber72RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 10) (by decide) ttFiber72ReverseRow_10_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_11_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk5] at h
  exact h.2

theorem ttFiber72ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 3) (ttFiber72StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 3) (ttFiber72StateAt 11)
      (ttFiber72RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 11) (by decide) ttFiber72ReverseRow_11_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_12_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk6] at h
  exact h.1

theorem ttFiber72ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 4) (ttFiber72StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 4) (ttFiber72StateAt 12)
      (ttFiber72RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 12) (by decide) ttFiber72ReverseRow_12_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_13_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk6] at h
  exact h.2

theorem ttFiber72ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 5) (ttFiber72StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 5) (ttFiber72StateAt 13)
      (ttFiber72RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 13) (by decide) ttFiber72ReverseRow_13_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_14_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk7] at h
  exact h.1

theorem ttFiber72ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 14)
      (ttFiber72RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 14) (by decide) ttFiber72ReverseRow_14_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_15_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk7] at h
  exact h.2

theorem ttFiber72ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 15)
      (ttFiber72RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 15) (by decide) ttFiber72ReverseRow_15_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_16_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk8] at h
  exact h.1

theorem ttFiber72ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 16)
      (ttFiber72RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 16) (by decide) ttFiber72ReverseRow_16_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_17_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk8] at h
  exact h.2

theorem ttFiber72ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 17)
      (ttFiber72RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 17) (by decide) ttFiber72ReverseRow_17_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_18_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk9] at h
  exact h.1

theorem ttFiber72ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 18)
      (ttFiber72RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 18) (by decide) ttFiber72ReverseRow_18_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_19_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk9] at h
  exact h.2

theorem ttFiber72ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 3) (ttFiber72StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 3) (ttFiber72StateAt 19)
      (ttFiber72RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 19) (by decide) ttFiber72ReverseRow_19_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_20_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk10] at h
  exact h.1

theorem ttFiber72ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 16) (ttFiber72StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 16) (ttFiber72StateAt 20)
      (ttFiber72RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 20) (by decide) ttFiber72ReverseRow_20_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_21_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk10] at h
  exact h.2

theorem ttFiber72ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 17) (ttFiber72StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 17) (ttFiber72StateAt 21)
      (ttFiber72RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 21) (by decide) ttFiber72ReverseRow_21_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_22_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk11] at h
  exact h.1

theorem ttFiber72ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 22)
      (ttFiber72RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 22) (by decide) ttFiber72ReverseRow_22_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_23_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk11] at h
  exact h.2

theorem ttFiber72ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 23)
      (ttFiber72RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 23) (by decide) ttFiber72ReverseRow_23_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_24_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk12] at h
  exact h.1

theorem ttFiber72ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 8) (ttFiber72StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 8) (ttFiber72StateAt 24)
      (ttFiber72RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 24) (by decide) ttFiber72ReverseRow_24_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_25_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk12] at h
  exact h.2

theorem ttFiber72ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 9) (ttFiber72StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 9) (ttFiber72StateAt 25)
      (ttFiber72RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 25) (by decide) ttFiber72ReverseRow_25_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_26_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk13] at h
  exact h.1

theorem ttFiber72ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 10) (ttFiber72StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 10) (ttFiber72StateAt 26)
      (ttFiber72RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 26) (by decide) ttFiber72ReverseRow_26_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_27_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk13] at h
  exact h.2

theorem ttFiber72ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 11) (ttFiber72StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 11) (ttFiber72StateAt 27)
      (ttFiber72RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 27) (by decide) ttFiber72ReverseRow_27_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_28_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk14] at h
  exact h.1

theorem ttFiber72ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 24) (ttFiber72StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 24) (ttFiber72StateAt 28)
      (ttFiber72RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 28) (by decide) ttFiber72ReverseRow_28_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_29_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk14] at h
  exact h.2

theorem ttFiber72ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 25) (ttFiber72StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 25) (ttFiber72StateAt 29)
      (ttFiber72RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 29) (by decide) ttFiber72ReverseRow_29_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_30_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk15] at h
  exact h.1

theorem ttFiber72ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 14) (ttFiber72StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 14) (ttFiber72StateAt 30)
      (ttFiber72RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 30) (by decide) ttFiber72ReverseRow_30_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_31_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk15] at h
  exact h.2

theorem ttFiber72ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 15) (ttFiber72StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 15) (ttFiber72StateAt 31)
      (ttFiber72RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 31) (by decide) ttFiber72ReverseRow_31_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_32_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk16] at h
  exact h.1

theorem ttFiber72ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 0) (ttFiber72StateAt 32)
      (ttFiber72RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 32) (by decide) ttFiber72ReverseRow_32_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_33_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk16] at h
  exact h.2

theorem ttFiber72ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 1) (ttFiber72StateAt 33)
      (ttFiber72RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 33) (by decide) ttFiber72ReverseRow_33_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_34_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk17] at h
  exact h.1

theorem ttFiber72ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 2) (ttFiber72StateAt 34)
      (ttFiber72RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 34) (by decide) ttFiber72ReverseRow_34_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_35_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk17] at h
  exact h.2

theorem ttFiber72ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 35)
      (ttFiber72RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 35) (by decide) ttFiber72ReverseRow_35_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_36_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk18] at h
  exact h.1

theorem ttFiber72ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 36)
      (ttFiber72RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 36) (by decide) ttFiber72ReverseRow_36_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_37_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk18] at h
  exact h.2

theorem ttFiber72ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 33) (ttFiber72StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 33) (ttFiber72StateAt 37)
      (ttFiber72RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 37) (by decide) ttFiber72ReverseRow_37_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_38_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk19] at h
  exact h.1

theorem ttFiber72ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 6) (ttFiber72StateAt 38)
      (ttFiber72RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 38) (by decide) ttFiber72ReverseRow_38_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_39_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk19] at h
  exact h.2

theorem ttFiber72ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 7) (ttFiber72StateAt 39)
      (ttFiber72RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 39) (by decide) ttFiber72ReverseRow_39_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_40_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk20] at h
  exact h.1

theorem ttFiber72ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 8) (ttFiber72StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 8) (ttFiber72StateAt 40)
      (ttFiber72RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 40) (by decide) ttFiber72ReverseRow_40_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_41_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk20] at h
  exact h.2

theorem ttFiber72ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 9) (ttFiber72StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 9) (ttFiber72StateAt 41)
      (ttFiber72RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 41) (by decide) ttFiber72ReverseRow_41_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_42_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk21] at h
  exact h.1

theorem ttFiber72ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 10) (ttFiber72StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 10) (ttFiber72StateAt 42)
      (ttFiber72RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 42) (by decide) ttFiber72ReverseRow_42_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_43_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk21] at h
  exact h.2

theorem ttFiber72ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 43)
      (ttFiber72RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 43) (by decide) ttFiber72ReverseRow_43_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_44_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk22] at h
  exact h.1

theorem ttFiber72ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 44)
      (ttFiber72RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 44) (by decide) ttFiber72ReverseRow_44_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_45_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk22] at h
  exact h.2

theorem ttFiber72ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 41) (ttFiber72StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 41) (ttFiber72StateAt 45)
      (ttFiber72RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 45) (by decide) ttFiber72ReverseRow_45_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_46_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk23] at h
  exact h.1

theorem ttFiber72ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 14) (ttFiber72StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 14) (ttFiber72StateAt 46)
      (ttFiber72RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 46) (by decide) ttFiber72ReverseRow_46_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_47_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk23] at h
  exact h.2

theorem ttFiber72ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 15) (ttFiber72StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 15) (ttFiber72StateAt 47)
      (ttFiber72RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 47) (by decide) ttFiber72ReverseRow_47_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_48_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk24] at h
  exact h.1

theorem ttFiber72ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 16) (ttFiber72StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 16) (ttFiber72StateAt 48)
      (ttFiber72RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 48) (by decide) ttFiber72ReverseRow_48_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_49_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk24] at h
  exact h.2

theorem ttFiber72ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 17) (ttFiber72StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 17) (ttFiber72StateAt 49)
      (ttFiber72RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 49) (by decide) ttFiber72ReverseRow_49_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_50_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk25] at h
  exact h.1

theorem ttFiber72ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 18) (ttFiber72StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 18) (ttFiber72StateAt 50)
      (ttFiber72RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 50) (by decide) ttFiber72ReverseRow_50_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_51_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk25] at h
  exact h.2

theorem ttFiber72ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 19) (ttFiber72StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 19) (ttFiber72StateAt 51)
      (ttFiber72RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 51) (by decide) ttFiber72ReverseRow_51_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_52_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk26] at h
  exact h.1

theorem ttFiber72ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 40) (ttFiber72StateAt 52)
      (ttFiber72RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 52) (by decide) ttFiber72ReverseRow_52_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_53_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk26] at h
  exact h.2

theorem ttFiber72ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 41) (ttFiber72StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 41) (ttFiber72StateAt 53)
      (ttFiber72RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 53) (by decide) ttFiber72ReverseRow_53_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_54_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk27] at h
  exact h.1

theorem ttFiber72ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 22) (ttFiber72StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 22) (ttFiber72StateAt 54)
      (ttFiber72RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 54) (by decide) ttFiber72ReverseRow_54_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_55_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk27] at h
  exact h.2

theorem ttFiber72ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 23) (ttFiber72StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 23) (ttFiber72StateAt 55)
      (ttFiber72RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 55) (by decide) ttFiber72ReverseRow_55_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_56_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk28] at h
  exact h.1

theorem ttFiber72ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 39) (ttFiber72StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 39) (ttFiber72StateAt 56)
      (ttFiber72RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 56) (by decide) ttFiber72ReverseRow_56_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_57_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk28] at h
  exact h.2

theorem ttFiber72ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 38) (ttFiber72StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 38) (ttFiber72StateAt 57)
      (ttFiber72RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 57) (by decide) ttFiber72ReverseRow_57_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_58_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk29] at h
  exact h.1

theorem ttFiber72ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 36) (ttFiber72StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 36) (ttFiber72StateAt 58)
      (ttFiber72RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 58) (by decide) ttFiber72ReverseRow_58_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_59_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk29] at h
  exact h.2

theorem ttFiber72ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 37) (ttFiber72StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 37) (ttFiber72StateAt 59)
      (ttFiber72RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 59) (by decide) ttFiber72ReverseRow_59_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_60_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk30] at h
  exact h.1

theorem ttFiber72ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 32) (ttFiber72StateAt 60)
      (ttFiber72RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 60) (by decide) ttFiber72ReverseRow_60_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_61_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk30] at h
  exact h.2

theorem ttFiber72ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 33) (ttFiber72StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 33) (ttFiber72StateAt 61)
      (ttFiber72RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 61) (by decide) ttFiber72ReverseRow_61_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_62_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk31] at h
  exact h.1

theorem ttFiber72ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 34) (ttFiber72StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 34) (ttFiber72StateAt 62)
      (ttFiber72RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 62) (by decide) ttFiber72ReverseRow_62_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72ReverseRow_63_ok' :
    directRowReverseValid ttFiber72Key ttFiber72Expected (ttFiber72RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber72Chunk31] at h
  exact h.2

theorem ttFiber72ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber72StateAt 35) (ttFiber72StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber72StateAt 35) (ttFiber72StateAt 63)
      (ttFiber72RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber72Key ttFiber72Expected
      (ttFiber72RowAt 63) (by decide) ttFiber72ReverseRow_63_ok'
    simpa [ttFiber72StateAt, ttFiber72RowAt, ttFiber72Rows, listGetD, directRow] using h

theorem ttFiber72FirstPassGrows :
    ((chainClosureStep ttWord ttFiber72DirectStates [ttFiber72StateAt 0]).length ==
      [ttFiber72StateAt 0].length) = false := by
  have hroot : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72DirectStates [ttFiber72StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber72DirectStates [ttFiber72StateAt 0]
      (ttFiber72StateAt 0) (by simp)
  have hnew : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72DirectStates [ttFiber72StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber72DirectStates [ttFiber72StateAt 0]
      (ttFiber72StateAt 0) (ttFiber72StateAt 1) (by decide) (by simp)
      ttFiber72ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber72DirectStates [ttFiber72StateAt 0])
    (ttFiber72StateAt 0) (ttFiber72StateAt 1) hroot hnew (by decide)

theorem ttFiber72State0_in_pass0_full :
    ttFiber72StateAt 0 ∈ [ttFiber72StateAt 0] := by
  simp

theorem ttFiber72State0_in_pass1_full :
    ttFiber72StateAt 0 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber72DirectStates
    ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full

theorem ttFiber72State1_in_pass1_prefix1 :
    ttFiber72StateAt 1 ∈ chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix0 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix0
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix1 = ttFiber72Prefix0 ++ [ttFiber72StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 1) []
    (chainClosureStep ttWord ttFiber72Prefix0 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep1

theorem ttFiber72State1_in_pass1_full :
    ttFiber72StateAt 1 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix1 ++ [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1

theorem ttFiber72State2_in_pass1_prefix2 :
    ttFiber72StateAt 2 ∈ chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix1
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix2 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 2) []
    (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep2

theorem ttFiber72State2_in_pass1_full :
    ttFiber72StateAt 2 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix2 ++ [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 2) ttFiber72State2_in_pass1_prefix2

theorem ttFiber72State3_in_pass1_prefix3 :
    ttFiber72StateAt 3 ∈ chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix2 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2]
      (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1
  rw [show ttFiber72Prefix3 = ttFiber72Prefix2 ++ [ttFiber72StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 3) []
    (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) hparentBefore ttFiber72ReverseSingleStep3

theorem ttFiber72State3_in_pass1_full :
    ttFiber72StateAt 3 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix3 ++ [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 3) ttFiber72State3_in_pass1_prefix3

theorem ttFiber72State4_in_pass1_prefix4 :
    ttFiber72StateAt 4 ∈ chainClosureStep ttWord ttFiber72Prefix4 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 2 ∈
      chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix3 = ttFiber72Prefix2 ++ [ttFiber72StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 3]
      (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 2) ttFiber72State2_in_pass1_prefix2
  rw [show ttFiber72Prefix4 = ttFiber72Prefix3 ++ [ttFiber72StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 4) []
    (chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 2) hparentBefore ttFiber72ReverseSingleStep4

theorem ttFiber72State4_in_pass1_full :
    ttFiber72StateAt 4 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix4 ++ [ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix4 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 4) ttFiber72State4_in_pass1_prefix4

theorem ttFiber72State6_in_pass1_prefix6 :
    ttFiber72StateAt 6 ∈ chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72Prefix5 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix5 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5]
      (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1
  rw [show ttFiber72Prefix6 = ttFiber72Prefix5 ++ [ttFiber72StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 6) []
    (chainClosureStep ttWord ttFiber72Prefix5 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) hparentBefore ttFiber72ReverseSingleStep6

theorem ttFiber72State6_in_pass1_full :
    ttFiber72StateAt 6 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix6 ++ [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 6) ttFiber72State6_in_pass1_prefix6

theorem ttFiber72State7_in_pass1_prefix7 :
    ttFiber72StateAt 7 ∈ chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix6
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix7 = ttFiber72Prefix6 ++ [ttFiber72StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 7) []
    (chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep7

theorem ttFiber72State7_in_pass1_full :
    ttFiber72StateAt 7 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix7 ++ [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 7) ttFiber72State7_in_pass1_prefix7

theorem ttFiber72State8_in_pass1_prefix8 :
    ttFiber72StateAt 8 ∈ chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix7
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix8 = ttFiber72Prefix7 ++ [ttFiber72StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 8) []
    (chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep8

theorem ttFiber72State8_in_pass1_full :
    ttFiber72StateAt 8 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix8 ++ [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 8) ttFiber72State8_in_pass1_prefix8

theorem ttFiber72State9_in_pass1_prefix9 :
    ttFiber72StateAt 9 ∈ chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix8 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8]
      (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1
  rw [show ttFiber72Prefix9 = ttFiber72Prefix8 ++ [ttFiber72StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 9) []
    (chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) hparentBefore ttFiber72ReverseSingleStep9

theorem ttFiber72State9_in_pass1_full :
    ttFiber72StateAt 9 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix9 ++ [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 9) ttFiber72State9_in_pass1_prefix9

theorem ttFiber72State10_in_pass1_prefix10 :
    ttFiber72StateAt 10 ∈ chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 2 ∈
      chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix9 = ttFiber72Prefix2 ++ [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9]
      (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 2) ttFiber72State2_in_pass1_prefix2
  rw [show ttFiber72Prefix10 = ttFiber72Prefix9 ++ [ttFiber72StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 10) []
    (chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 2) hparentBefore ttFiber72ReverseSingleStep10

theorem ttFiber72State10_in_pass1_full :
    ttFiber72StateAt 10 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix10 ++ [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 10) ttFiber72State10_in_pass1_prefix10

theorem ttFiber72State11_in_pass1_prefix11 :
    ttFiber72StateAt 11 ∈ chainClosureStep ttWord ttFiber72Prefix11 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 3 ∈
      chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix10 = ttFiber72Prefix3 ++ [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10]
      (chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 3) ttFiber72State3_in_pass1_prefix3
  rw [show ttFiber72Prefix11 = ttFiber72Prefix10 ++ [ttFiber72StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 11) []
    (chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 3) hparentBefore ttFiber72ReverseSingleStep11

theorem ttFiber72State11_in_pass1_full :
    ttFiber72StateAt 11 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix11 ++ [ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix11 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 11) ttFiber72State11_in_pass1_prefix11

theorem ttFiber72State12_in_pass1_prefix12 :
    ttFiber72StateAt 12 ∈ chainClosureStep ttWord ttFiber72Prefix12 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 4 ∈
      chainClosureStep ttWord ttFiber72Prefix11 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix11 = ttFiber72Prefix4 ++ [ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11]
      (chainClosureStep ttWord ttFiber72Prefix4 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 4) ttFiber72State4_in_pass1_prefix4
  rw [show ttFiber72Prefix12 = ttFiber72Prefix11 ++ [ttFiber72StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 12) []
    (chainClosureStep ttWord ttFiber72Prefix11 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 4) hparentBefore ttFiber72ReverseSingleStep12

theorem ttFiber72State12_in_pass1_full :
    ttFiber72StateAt 12 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix12 ++ [ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix12 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 12) ttFiber72State12_in_pass1_prefix12

theorem ttFiber72State14_in_pass1_prefix14 :
    ttFiber72StateAt 14 ∈ chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 6 ∈
      chainClosureStep ttWord ttFiber72Prefix13 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix13 = ttFiber72Prefix6 ++ [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13]
      (chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 6) ttFiber72State6_in_pass1_prefix6
  rw [show ttFiber72Prefix14 = ttFiber72Prefix13 ++ [ttFiber72StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 14) []
    (chainClosureStep ttWord ttFiber72Prefix13 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 6) hparentBefore ttFiber72ReverseSingleStep14

theorem ttFiber72State14_in_pass1_full :
    ttFiber72StateAt 14 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix14 ++ [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 14) ttFiber72State14_in_pass1_prefix14

theorem ttFiber72State15_in_pass1_prefix15 :
    ttFiber72StateAt 15 ∈ chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 7 ∈
      chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix14 = ttFiber72Prefix7 ++ [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14]
      (chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 7) ttFiber72State7_in_pass1_prefix7
  rw [show ttFiber72Prefix15 = ttFiber72Prefix14 ++ [ttFiber72StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 15) []
    (chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 7) hparentBefore ttFiber72ReverseSingleStep15

theorem ttFiber72State15_in_pass1_full :
    ttFiber72StateAt 15 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix15 ++ [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 15) ttFiber72State15_in_pass1_prefix15

theorem ttFiber72State16_in_pass1_prefix16 :
    ttFiber72StateAt 16 ∈ chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix15
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix16 = ttFiber72Prefix15 ++ [ttFiber72StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 16) []
    (chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep16

theorem ttFiber72State16_in_pass1_full :
    ttFiber72StateAt 16 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix16 ++ [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 16) ttFiber72State16_in_pass1_prefix16

theorem ttFiber72State17_in_pass1_prefix17 :
    ttFiber72StateAt 17 ∈ chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix16 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16]
      (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1
  rw [show ttFiber72Prefix17 = ttFiber72Prefix16 ++ [ttFiber72StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 17) []
    (chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) hparentBefore ttFiber72ReverseSingleStep17

theorem ttFiber72State17_in_pass1_full :
    ttFiber72StateAt 17 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix17 ++ [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 17) ttFiber72State17_in_pass1_prefix17

theorem ttFiber72State18_in_pass1_prefix18 :
    ttFiber72StateAt 18 ∈ chainClosureStep ttWord ttFiber72Prefix18 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 2 ∈
      chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix17 = ttFiber72Prefix2 ++ [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17]
      (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 2) ttFiber72State2_in_pass1_prefix2
  rw [show ttFiber72Prefix18 = ttFiber72Prefix17 ++ [ttFiber72StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 18) []
    (chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 2) hparentBefore ttFiber72ReverseSingleStep18

theorem ttFiber72State18_in_pass1_full :
    ttFiber72StateAt 18 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix18 ++ [ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix18 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 18) ttFiber72State18_in_pass1_prefix18

theorem ttFiber72State19_in_pass1_prefix19 :
    ttFiber72StateAt 19 ∈ chainClosureStep ttWord ttFiber72Prefix19 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 3 ∈
      chainClosureStep ttWord ttFiber72Prefix18 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix18 = ttFiber72Prefix3 ++ [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18]
      (chainClosureStep ttWord ttFiber72Prefix3 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 3) ttFiber72State3_in_pass1_prefix3
  rw [show ttFiber72Prefix19 = ttFiber72Prefix18 ++ [ttFiber72StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 19) []
    (chainClosureStep ttWord ttFiber72Prefix18 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 3) hparentBefore ttFiber72ReverseSingleStep19

theorem ttFiber72State19_in_pass1_full :
    ttFiber72StateAt 19 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix19 ++ [ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix19 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 19) ttFiber72State19_in_pass1_prefix19

theorem ttFiber72State20_in_pass1_prefix20 :
    ttFiber72StateAt 20 ∈ chainClosureStep ttWord ttFiber72Prefix20 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 16 ∈
      chainClosureStep ttWord ttFiber72Prefix19 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix19 = ttFiber72Prefix16 ++ [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19]
      (chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 16) ttFiber72State16_in_pass1_prefix16
  rw [show ttFiber72Prefix20 = ttFiber72Prefix19 ++ [ttFiber72StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 20) []
    (chainClosureStep ttWord ttFiber72Prefix19 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 16) hparentBefore ttFiber72ReverseSingleStep20

theorem ttFiber72State20_in_pass1_full :
    ttFiber72StateAt 20 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix20 ++ [ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix20 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 20) ttFiber72State20_in_pass1_prefix20

theorem ttFiber72State21_in_pass1_prefix21 :
    ttFiber72StateAt 21 ∈ chainClosureStep ttWord ttFiber72Prefix21 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 17 ∈
      chainClosureStep ttWord ttFiber72Prefix20 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix20 = ttFiber72Prefix17 ++ [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20]
      (chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 17) ttFiber72State17_in_pass1_prefix17
  rw [show ttFiber72Prefix21 = ttFiber72Prefix20 ++ [ttFiber72StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 21) []
    (chainClosureStep ttWord ttFiber72Prefix20 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 17) hparentBefore ttFiber72ReverseSingleStep21

theorem ttFiber72State21_in_pass1_full :
    ttFiber72StateAt 21 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix21 ++ [ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix21 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 21) ttFiber72State21_in_pass1_prefix21

theorem ttFiber72State22_in_pass1_prefix22 :
    ttFiber72StateAt 22 ∈ chainClosureStep ttWord ttFiber72Prefix22 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 6 ∈
      chainClosureStep ttWord ttFiber72Prefix21 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix21 = ttFiber72Prefix6 ++ [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21]
      (chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 6) ttFiber72State6_in_pass1_prefix6
  rw [show ttFiber72Prefix22 = ttFiber72Prefix21 ++ [ttFiber72StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 22) []
    (chainClosureStep ttWord ttFiber72Prefix21 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 6) hparentBefore ttFiber72ReverseSingleStep22

theorem ttFiber72State22_in_pass1_full :
    ttFiber72StateAt 22 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix22 ++ [ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix22 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 22) ttFiber72State22_in_pass1_prefix22

theorem ttFiber72State23_in_pass1_prefix23 :
    ttFiber72StateAt 23 ∈ chainClosureStep ttWord ttFiber72Prefix23 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 7 ∈
      chainClosureStep ttWord ttFiber72Prefix22 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix22 = ttFiber72Prefix7 ++ [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22]
      (chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 7) ttFiber72State7_in_pass1_prefix7
  rw [show ttFiber72Prefix23 = ttFiber72Prefix22 ++ [ttFiber72StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 23) []
    (chainClosureStep ttWord ttFiber72Prefix22 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 7) hparentBefore ttFiber72ReverseSingleStep23

theorem ttFiber72State23_in_pass1_full :
    ttFiber72StateAt 23 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix23 ++ [ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix23 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 23) ttFiber72State23_in_pass1_prefix23

theorem ttFiber72State24_in_pass1_prefix24 :
    ttFiber72StateAt 24 ∈ chainClosureStep ttWord ttFiber72Prefix24 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 8 ∈
      chainClosureStep ttWord ttFiber72Prefix23 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix23 = ttFiber72Prefix8 ++ [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23]
      (chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 8) ttFiber72State8_in_pass1_prefix8
  rw [show ttFiber72Prefix24 = ttFiber72Prefix23 ++ [ttFiber72StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 24) []
    (chainClosureStep ttWord ttFiber72Prefix23 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 8) hparentBefore ttFiber72ReverseSingleStep24

theorem ttFiber72State24_in_pass1_full :
    ttFiber72StateAt 24 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix24 ++ [ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix24 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 24) ttFiber72State24_in_pass1_prefix24

theorem ttFiber72State25_in_pass1_prefix25 :
    ttFiber72StateAt 25 ∈ chainClosureStep ttWord ttFiber72Prefix25 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 9 ∈
      chainClosureStep ttWord ttFiber72Prefix24 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix24 = ttFiber72Prefix9 ++ [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24]
      (chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 9) ttFiber72State9_in_pass1_prefix9
  rw [show ttFiber72Prefix25 = ttFiber72Prefix24 ++ [ttFiber72StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 25) []
    (chainClosureStep ttWord ttFiber72Prefix24 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 9) hparentBefore ttFiber72ReverseSingleStep25

theorem ttFiber72State25_in_pass1_full :
    ttFiber72StateAt 25 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix25 ++ [ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix25 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 25) ttFiber72State25_in_pass1_prefix25

theorem ttFiber72State26_in_pass1_prefix26 :
    ttFiber72StateAt 26 ∈ chainClosureStep ttWord ttFiber72Prefix26 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 10 ∈
      chainClosureStep ttWord ttFiber72Prefix25 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix25 = ttFiber72Prefix10 ++ [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25]
      (chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 10) ttFiber72State10_in_pass1_prefix10
  rw [show ttFiber72Prefix26 = ttFiber72Prefix25 ++ [ttFiber72StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 26) []
    (chainClosureStep ttWord ttFiber72Prefix25 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 10) hparentBefore ttFiber72ReverseSingleStep26

theorem ttFiber72State26_in_pass1_full :
    ttFiber72StateAt 26 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix26 ++ [ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix26 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 26) ttFiber72State26_in_pass1_prefix26

theorem ttFiber72State27_in_pass1_prefix27 :
    ttFiber72StateAt 27 ∈ chainClosureStep ttWord ttFiber72Prefix27 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 11 ∈
      chainClosureStep ttWord ttFiber72Prefix26 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix26 = ttFiber72Prefix11 ++ [ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26]
      (chainClosureStep ttWord ttFiber72Prefix11 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 11) ttFiber72State11_in_pass1_prefix11
  rw [show ttFiber72Prefix27 = ttFiber72Prefix26 ++ [ttFiber72StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 27) []
    (chainClosureStep ttWord ttFiber72Prefix26 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 11) hparentBefore ttFiber72ReverseSingleStep27

theorem ttFiber72State27_in_pass1_full :
    ttFiber72StateAt 27 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix27 ++ [ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix27 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 27) ttFiber72State27_in_pass1_prefix27

theorem ttFiber72State28_in_pass1_prefix28 :
    ttFiber72StateAt 28 ∈ chainClosureStep ttWord ttFiber72Prefix28 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 24 ∈
      chainClosureStep ttWord ttFiber72Prefix27 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix27 = ttFiber72Prefix24 ++ [ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27]
      (chainClosureStep ttWord ttFiber72Prefix24 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 24) ttFiber72State24_in_pass1_prefix24
  rw [show ttFiber72Prefix28 = ttFiber72Prefix27 ++ [ttFiber72StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 28) []
    (chainClosureStep ttWord ttFiber72Prefix27 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 24) hparentBefore ttFiber72ReverseSingleStep28

theorem ttFiber72State28_in_pass1_full :
    ttFiber72StateAt 28 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix28 ++ [ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix28 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 28) ttFiber72State28_in_pass1_prefix28

theorem ttFiber72State29_in_pass1_prefix29 :
    ttFiber72StateAt 29 ∈ chainClosureStep ttWord ttFiber72Prefix29 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 25 ∈
      chainClosureStep ttWord ttFiber72Prefix28 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix28 = ttFiber72Prefix25 ++ [ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28]
      (chainClosureStep ttWord ttFiber72Prefix25 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 25) ttFiber72State25_in_pass1_prefix25
  rw [show ttFiber72Prefix29 = ttFiber72Prefix28 ++ [ttFiber72StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 29) []
    (chainClosureStep ttWord ttFiber72Prefix28 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 25) hparentBefore ttFiber72ReverseSingleStep29

theorem ttFiber72State29_in_pass1_full :
    ttFiber72StateAt 29 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix29 ++ [ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix29 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 29) ttFiber72State29_in_pass1_prefix29

theorem ttFiber72State30_in_pass1_prefix30 :
    ttFiber72StateAt 30 ∈ chainClosureStep ttWord ttFiber72Prefix30 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 14 ∈
      chainClosureStep ttWord ttFiber72Prefix29 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix29 = ttFiber72Prefix14 ++ [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29]
      (chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 14) ttFiber72State14_in_pass1_prefix14
  rw [show ttFiber72Prefix30 = ttFiber72Prefix29 ++ [ttFiber72StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 30) []
    (chainClosureStep ttWord ttFiber72Prefix29 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 14) hparentBefore ttFiber72ReverseSingleStep30

theorem ttFiber72State30_in_pass1_full :
    ttFiber72StateAt 30 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix30 ++ [ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix30 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 30) ttFiber72State30_in_pass1_prefix30

theorem ttFiber72State31_in_pass1_prefix31 :
    ttFiber72StateAt 31 ∈ chainClosureStep ttWord ttFiber72Prefix31 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 15 ∈
      chainClosureStep ttWord ttFiber72Prefix30 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix30 = ttFiber72Prefix15 ++ [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30]
      (chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 15) ttFiber72State15_in_pass1_prefix15
  rw [show ttFiber72Prefix31 = ttFiber72Prefix30 ++ [ttFiber72StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 31) []
    (chainClosureStep ttWord ttFiber72Prefix30 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 15) hparentBefore ttFiber72ReverseSingleStep31

theorem ttFiber72State31_in_pass1_full :
    ttFiber72StateAt 31 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix31 ++ [ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix31 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 31) ttFiber72State31_in_pass1_prefix31

theorem ttFiber72State32_in_pass1_prefix32 :
    ttFiber72StateAt 32 ∈ chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 0 ∈
      chainClosureStep ttWord ttFiber72Prefix31 ([ttFiber72StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix31
      ([ttFiber72StateAt 0]) (ttFiber72StateAt 0) ttFiber72State0_in_pass0_full
  rw [show ttFiber72Prefix32 = ttFiber72Prefix31 ++ [ttFiber72StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 32) []
    (chainClosureStep ttWord ttFiber72Prefix31 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 0) hparentBefore ttFiber72ReverseSingleStep32

theorem ttFiber72State32_in_pass1_full :
    ttFiber72StateAt 32 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix32 ++ [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 32) ttFiber72State32_in_pass1_prefix32

theorem ttFiber72State33_in_pass1_prefix33 :
    ttFiber72StateAt 33 ∈ chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 1 ∈
      chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix32 = ttFiber72Prefix1 ++ [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 2, ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32]
      (chainClosureStep ttWord ttFiber72Prefix1 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 1) ttFiber72State1_in_pass1_prefix1
  rw [show ttFiber72Prefix33 = ttFiber72Prefix32 ++ [ttFiber72StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 33) []
    (chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 1) hparentBefore ttFiber72ReverseSingleStep33

theorem ttFiber72State33_in_pass1_full :
    ttFiber72StateAt 33 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix33 ++ [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 33) ttFiber72State33_in_pass1_prefix33

theorem ttFiber72State34_in_pass1_prefix34 :
    ttFiber72StateAt 34 ∈ chainClosureStep ttWord ttFiber72Prefix34 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 2 ∈
      chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix33 = ttFiber72Prefix2 ++ [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 3, ttFiber72StateAt 4, ttFiber72StateAt 5, ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33]
      (chainClosureStep ttWord ttFiber72Prefix2 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 2) ttFiber72State2_in_pass1_prefix2
  rw [show ttFiber72Prefix34 = ttFiber72Prefix33 ++ [ttFiber72StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 34) []
    (chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 2) hparentBefore ttFiber72ReverseSingleStep34

theorem ttFiber72State34_in_pass1_full :
    ttFiber72StateAt 34 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix34 ++ [ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix34 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 34) ttFiber72State34_in_pass1_prefix34

theorem ttFiber72State35_in_pass1_prefix35 :
    ttFiber72StateAt 35 ∈ chainClosureStep ttWord ttFiber72Prefix35 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 32 ∈
      chainClosureStep ttWord ttFiber72Prefix34 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix34 = ttFiber72Prefix32 ++ [ttFiber72StateAt 33, ttFiber72StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 33, ttFiber72StateAt 34]
      (chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 32) ttFiber72State32_in_pass1_prefix32
  rw [show ttFiber72Prefix35 = ttFiber72Prefix34 ++ [ttFiber72StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 35) []
    (chainClosureStep ttWord ttFiber72Prefix34 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 32) hparentBefore ttFiber72ReverseSingleStep35

theorem ttFiber72State35_in_pass1_full :
    ttFiber72StateAt 35 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix35 ++ [ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix35 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 35) ttFiber72State35_in_pass1_prefix35

theorem ttFiber72State36_in_pass1_prefix36 :
    ttFiber72StateAt 36 ∈ chainClosureStep ttWord ttFiber72Prefix36 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 32 ∈
      chainClosureStep ttWord ttFiber72Prefix35 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix35 = ttFiber72Prefix32 ++ [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35]
      (chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 32) ttFiber72State32_in_pass1_prefix32
  rw [show ttFiber72Prefix36 = ttFiber72Prefix35 ++ [ttFiber72StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 36) []
    (chainClosureStep ttWord ttFiber72Prefix35 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 32) hparentBefore ttFiber72ReverseSingleStep36

theorem ttFiber72State36_in_pass1_full :
    ttFiber72StateAt 36 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix36 ++ [ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix36 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 36) ttFiber72State36_in_pass1_prefix36

theorem ttFiber72State37_in_pass1_prefix37 :
    ttFiber72StateAt 37 ∈ chainClosureStep ttWord ttFiber72Prefix37 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 33 ∈
      chainClosureStep ttWord ttFiber72Prefix36 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix36 = ttFiber72Prefix33 ++ [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36]
      (chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 33) ttFiber72State33_in_pass1_prefix33
  rw [show ttFiber72Prefix37 = ttFiber72Prefix36 ++ [ttFiber72StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 37) []
    (chainClosureStep ttWord ttFiber72Prefix36 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 33) hparentBefore ttFiber72ReverseSingleStep37

theorem ttFiber72State37_in_pass1_full :
    ttFiber72StateAt 37 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix37 ++ [ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix37 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 37) ttFiber72State37_in_pass1_prefix37

theorem ttFiber72State38_in_pass1_prefix38 :
    ttFiber72StateAt 38 ∈ chainClosureStep ttWord ttFiber72Prefix38 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 6 ∈
      chainClosureStep ttWord ttFiber72Prefix37 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix37 = ttFiber72Prefix6 ++ [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37]
      (chainClosureStep ttWord ttFiber72Prefix6 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 6) ttFiber72State6_in_pass1_prefix6
  rw [show ttFiber72Prefix38 = ttFiber72Prefix37 ++ [ttFiber72StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 38) []
    (chainClosureStep ttWord ttFiber72Prefix37 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 6) hparentBefore ttFiber72ReverseSingleStep38

theorem ttFiber72State38_in_pass1_full :
    ttFiber72StateAt 38 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix38 ++ [ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix38 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 38) ttFiber72State38_in_pass1_prefix38

theorem ttFiber72State39_in_pass1_prefix39 :
    ttFiber72StateAt 39 ∈ chainClosureStep ttWord ttFiber72Prefix39 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 7 ∈
      chainClosureStep ttWord ttFiber72Prefix38 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix38 = ttFiber72Prefix7 ++ [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38]
      (chainClosureStep ttWord ttFiber72Prefix7 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 7) ttFiber72State7_in_pass1_prefix7
  rw [show ttFiber72Prefix39 = ttFiber72Prefix38 ++ [ttFiber72StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 39) []
    (chainClosureStep ttWord ttFiber72Prefix38 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 7) hparentBefore ttFiber72ReverseSingleStep39

theorem ttFiber72State39_in_pass1_full :
    ttFiber72StateAt 39 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix39 ++ [ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix39 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 39) ttFiber72State39_in_pass1_prefix39

theorem ttFiber72State40_in_pass1_prefix40 :
    ttFiber72StateAt 40 ∈ chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 8 ∈
      chainClosureStep ttWord ttFiber72Prefix39 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix39 = ttFiber72Prefix8 ++ [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39]
      (chainClosureStep ttWord ttFiber72Prefix8 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 8) ttFiber72State8_in_pass1_prefix8
  rw [show ttFiber72Prefix40 = ttFiber72Prefix39 ++ [ttFiber72StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 40) []
    (chainClosureStep ttWord ttFiber72Prefix39 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 8) hparentBefore ttFiber72ReverseSingleStep40

theorem ttFiber72State40_in_pass1_full :
    ttFiber72StateAt 40 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix40 ++ [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 40) ttFiber72State40_in_pass1_prefix40

theorem ttFiber72State41_in_pass1_prefix41 :
    ttFiber72StateAt 41 ∈ chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 9 ∈
      chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix40 = ttFiber72Prefix9 ++ [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40]
      (chainClosureStep ttWord ttFiber72Prefix9 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 9) ttFiber72State9_in_pass1_prefix9
  rw [show ttFiber72Prefix41 = ttFiber72Prefix40 ++ [ttFiber72StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 41) []
    (chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 9) hparentBefore ttFiber72ReverseSingleStep41

theorem ttFiber72State41_in_pass1_full :
    ttFiber72StateAt 41 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix41 ++ [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 41) ttFiber72State41_in_pass1_prefix41

theorem ttFiber72State42_in_pass1_prefix42 :
    ttFiber72StateAt 42 ∈ chainClosureStep ttWord ttFiber72Prefix42 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 10 ∈
      chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix41 = ttFiber72Prefix10 ++ [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41]
      (chainClosureStep ttWord ttFiber72Prefix10 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 10) ttFiber72State10_in_pass1_prefix10
  rw [show ttFiber72Prefix42 = ttFiber72Prefix41 ++ [ttFiber72StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 42) []
    (chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 10) hparentBefore ttFiber72ReverseSingleStep42

theorem ttFiber72State42_in_pass1_full :
    ttFiber72StateAt 42 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix42 ++ [ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix42 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 42) ttFiber72State42_in_pass1_prefix42

theorem ttFiber72State43_in_pass1_prefix43 :
    ttFiber72StateAt 43 ∈ chainClosureStep ttWord ttFiber72Prefix43 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 40 ∈
      chainClosureStep ttWord ttFiber72Prefix42 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix42 = ttFiber72Prefix40 ++ [ttFiber72StateAt 41, ttFiber72StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 41, ttFiber72StateAt 42]
      (chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 40) ttFiber72State40_in_pass1_prefix40
  rw [show ttFiber72Prefix43 = ttFiber72Prefix42 ++ [ttFiber72StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 43) []
    (chainClosureStep ttWord ttFiber72Prefix42 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 40) hparentBefore ttFiber72ReverseSingleStep43

theorem ttFiber72State43_in_pass1_full :
    ttFiber72StateAt 43 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix43 ++ [ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix43 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 43) ttFiber72State43_in_pass1_prefix43

theorem ttFiber72State44_in_pass1_prefix44 :
    ttFiber72StateAt 44 ∈ chainClosureStep ttWord ttFiber72Prefix44 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 40 ∈
      chainClosureStep ttWord ttFiber72Prefix43 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix43 = ttFiber72Prefix40 ++ [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43]
      (chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 40) ttFiber72State40_in_pass1_prefix40
  rw [show ttFiber72Prefix44 = ttFiber72Prefix43 ++ [ttFiber72StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 44) []
    (chainClosureStep ttWord ttFiber72Prefix43 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 40) hparentBefore ttFiber72ReverseSingleStep44

theorem ttFiber72State44_in_pass1_full :
    ttFiber72StateAt 44 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix44 ++ [ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix44 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 44) ttFiber72State44_in_pass1_prefix44

theorem ttFiber72State45_in_pass1_prefix45 :
    ttFiber72StateAt 45 ∈ chainClosureStep ttWord ttFiber72Prefix45 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 41 ∈
      chainClosureStep ttWord ttFiber72Prefix44 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix44 = ttFiber72Prefix41 ++ [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44]
      (chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 41) ttFiber72State41_in_pass1_prefix41
  rw [show ttFiber72Prefix45 = ttFiber72Prefix44 ++ [ttFiber72StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 45) []
    (chainClosureStep ttWord ttFiber72Prefix44 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 41) hparentBefore ttFiber72ReverseSingleStep45

theorem ttFiber72State45_in_pass1_full :
    ttFiber72StateAt 45 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix45 ++ [ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix45 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 45) ttFiber72State45_in_pass1_prefix45

theorem ttFiber72State46_in_pass1_prefix46 :
    ttFiber72StateAt 46 ∈ chainClosureStep ttWord ttFiber72Prefix46 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 14 ∈
      chainClosureStep ttWord ttFiber72Prefix45 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix45 = ttFiber72Prefix14 ++ [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45]
      (chainClosureStep ttWord ttFiber72Prefix14 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 14) ttFiber72State14_in_pass1_prefix14
  rw [show ttFiber72Prefix46 = ttFiber72Prefix45 ++ [ttFiber72StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 46) []
    (chainClosureStep ttWord ttFiber72Prefix45 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 14) hparentBefore ttFiber72ReverseSingleStep46

theorem ttFiber72State46_in_pass1_full :
    ttFiber72StateAt 46 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix46 ++ [ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix46 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 46) ttFiber72State46_in_pass1_prefix46

theorem ttFiber72State47_in_pass1_prefix47 :
    ttFiber72StateAt 47 ∈ chainClosureStep ttWord ttFiber72Prefix47 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 15 ∈
      chainClosureStep ttWord ttFiber72Prefix46 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix46 = ttFiber72Prefix15 ++ [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46]
      (chainClosureStep ttWord ttFiber72Prefix15 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 15) ttFiber72State15_in_pass1_prefix15
  rw [show ttFiber72Prefix47 = ttFiber72Prefix46 ++ [ttFiber72StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 47) []
    (chainClosureStep ttWord ttFiber72Prefix46 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 15) hparentBefore ttFiber72ReverseSingleStep47

theorem ttFiber72State47_in_pass1_full :
    ttFiber72StateAt 47 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix47 ++ [ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix47 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 47) ttFiber72State47_in_pass1_prefix47

theorem ttFiber72State48_in_pass1_prefix48 :
    ttFiber72StateAt 48 ∈ chainClosureStep ttWord ttFiber72Prefix48 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 16 ∈
      chainClosureStep ttWord ttFiber72Prefix47 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix47 = ttFiber72Prefix16 ++ [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47]
      (chainClosureStep ttWord ttFiber72Prefix16 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 16) ttFiber72State16_in_pass1_prefix16
  rw [show ttFiber72Prefix48 = ttFiber72Prefix47 ++ [ttFiber72StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 48) []
    (chainClosureStep ttWord ttFiber72Prefix47 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 16) hparentBefore ttFiber72ReverseSingleStep48

theorem ttFiber72State48_in_pass1_full :
    ttFiber72StateAt 48 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix48 ++ [ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix48 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 48) ttFiber72State48_in_pass1_prefix48

theorem ttFiber72State49_in_pass1_prefix49 :
    ttFiber72StateAt 49 ∈ chainClosureStep ttWord ttFiber72Prefix49 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 17 ∈
      chainClosureStep ttWord ttFiber72Prefix48 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix48 = ttFiber72Prefix17 ++ [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48]
      (chainClosureStep ttWord ttFiber72Prefix17 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 17) ttFiber72State17_in_pass1_prefix17
  rw [show ttFiber72Prefix49 = ttFiber72Prefix48 ++ [ttFiber72StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 49) []
    (chainClosureStep ttWord ttFiber72Prefix48 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 17) hparentBefore ttFiber72ReverseSingleStep49

theorem ttFiber72State49_in_pass1_full :
    ttFiber72StateAt 49 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix49 ++ [ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix49 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 49) ttFiber72State49_in_pass1_prefix49

theorem ttFiber72State50_in_pass1_prefix50 :
    ttFiber72StateAt 50 ∈ chainClosureStep ttWord ttFiber72Prefix50 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 18 ∈
      chainClosureStep ttWord ttFiber72Prefix49 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix49 = ttFiber72Prefix18 ++ [ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49]
      (chainClosureStep ttWord ttFiber72Prefix18 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 18) ttFiber72State18_in_pass1_prefix18
  rw [show ttFiber72Prefix50 = ttFiber72Prefix49 ++ [ttFiber72StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 50) []
    (chainClosureStep ttWord ttFiber72Prefix49 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 18) hparentBefore ttFiber72ReverseSingleStep50

theorem ttFiber72State50_in_pass1_full :
    ttFiber72StateAt 50 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix50 ++ [ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix50 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 50) ttFiber72State50_in_pass1_prefix50

theorem ttFiber72State51_in_pass1_prefix51 :
    ttFiber72StateAt 51 ∈ chainClosureStep ttWord ttFiber72Prefix51 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 19 ∈
      chainClosureStep ttWord ttFiber72Prefix50 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix50 = ttFiber72Prefix19 ++ [ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50]
      (chainClosureStep ttWord ttFiber72Prefix19 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 19) ttFiber72State19_in_pass1_prefix19
  rw [show ttFiber72Prefix51 = ttFiber72Prefix50 ++ [ttFiber72StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 51) []
    (chainClosureStep ttWord ttFiber72Prefix50 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 19) hparentBefore ttFiber72ReverseSingleStep51

theorem ttFiber72State51_in_pass1_full :
    ttFiber72StateAt 51 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix51 ++ [ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix51 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 51) ttFiber72State51_in_pass1_prefix51

theorem ttFiber72State52_in_pass1_prefix52 :
    ttFiber72StateAt 52 ∈ chainClosureStep ttWord ttFiber72Prefix52 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 40 ∈
      chainClosureStep ttWord ttFiber72Prefix51 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix51 = ttFiber72Prefix40 ++ [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51]
      (chainClosureStep ttWord ttFiber72Prefix40 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 40) ttFiber72State40_in_pass1_prefix40
  rw [show ttFiber72Prefix52 = ttFiber72Prefix51 ++ [ttFiber72StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 52) []
    (chainClosureStep ttWord ttFiber72Prefix51 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 40) hparentBefore ttFiber72ReverseSingleStep52

theorem ttFiber72State52_in_pass1_full :
    ttFiber72StateAt 52 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix52 ++ [ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix52 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 52) ttFiber72State52_in_pass1_prefix52

theorem ttFiber72State53_in_pass1_prefix53 :
    ttFiber72StateAt 53 ∈ chainClosureStep ttWord ttFiber72Prefix53 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 41 ∈
      chainClosureStep ttWord ttFiber72Prefix52 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix52 = ttFiber72Prefix41 ++ [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52]
      (chainClosureStep ttWord ttFiber72Prefix41 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 41) ttFiber72State41_in_pass1_prefix41
  rw [show ttFiber72Prefix53 = ttFiber72Prefix52 ++ [ttFiber72StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 53) []
    (chainClosureStep ttWord ttFiber72Prefix52 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 41) hparentBefore ttFiber72ReverseSingleStep53

theorem ttFiber72State53_in_pass1_full :
    ttFiber72StateAt 53 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix53 ++ [ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix53 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 53) ttFiber72State53_in_pass1_prefix53

theorem ttFiber72State54_in_pass1_prefix54 :
    ttFiber72StateAt 54 ∈ chainClosureStep ttWord ttFiber72Prefix54 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 22 ∈
      chainClosureStep ttWord ttFiber72Prefix53 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix53 = ttFiber72Prefix22 ++ [ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53]
      (chainClosureStep ttWord ttFiber72Prefix22 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 22) ttFiber72State22_in_pass1_prefix22
  rw [show ttFiber72Prefix54 = ttFiber72Prefix53 ++ [ttFiber72StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 54) []
    (chainClosureStep ttWord ttFiber72Prefix53 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 22) hparentBefore ttFiber72ReverseSingleStep54

theorem ttFiber72State54_in_pass1_full :
    ttFiber72StateAt 54 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix54 ++ [ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix54 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 54) ttFiber72State54_in_pass1_prefix54

theorem ttFiber72State55_in_pass1_prefix55 :
    ttFiber72StateAt 55 ∈ chainClosureStep ttWord ttFiber72Prefix55 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 23 ∈
      chainClosureStep ttWord ttFiber72Prefix54 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix54 = ttFiber72Prefix23 ++ [ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54]
      (chainClosureStep ttWord ttFiber72Prefix23 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 23) ttFiber72State23_in_pass1_prefix23
  rw [show ttFiber72Prefix55 = ttFiber72Prefix54 ++ [ttFiber72StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 55) []
    (chainClosureStep ttWord ttFiber72Prefix54 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 23) hparentBefore ttFiber72ReverseSingleStep55

theorem ttFiber72State55_in_pass1_full :
    ttFiber72StateAt 55 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix55 ++ [ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix55 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 55) ttFiber72State55_in_pass1_prefix55

theorem ttFiber72State56_in_pass1_prefix56 :
    ttFiber72StateAt 56 ∈ chainClosureStep ttWord ttFiber72Prefix56 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 39 ∈
      chainClosureStep ttWord ttFiber72Prefix55 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix55 = ttFiber72Prefix39 ++ [ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55]
      (chainClosureStep ttWord ttFiber72Prefix39 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 39) ttFiber72State39_in_pass1_prefix39
  rw [show ttFiber72Prefix56 = ttFiber72Prefix55 ++ [ttFiber72StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 56) []
    (chainClosureStep ttWord ttFiber72Prefix55 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 39) hparentBefore ttFiber72ReverseSingleStep56

theorem ttFiber72State56_in_pass1_full :
    ttFiber72StateAt 56 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix56 ++ [ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix56 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 56) ttFiber72State56_in_pass1_prefix56

theorem ttFiber72State57_in_pass1_prefix57 :
    ttFiber72StateAt 57 ∈ chainClosureStep ttWord ttFiber72Prefix57 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 38 ∈
      chainClosureStep ttWord ttFiber72Prefix56 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix56 = ttFiber72Prefix38 ++ [ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56]
      (chainClosureStep ttWord ttFiber72Prefix38 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 38) ttFiber72State38_in_pass1_prefix38
  rw [show ttFiber72Prefix57 = ttFiber72Prefix56 ++ [ttFiber72StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 57) []
    (chainClosureStep ttWord ttFiber72Prefix56 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 38) hparentBefore ttFiber72ReverseSingleStep57

theorem ttFiber72State57_in_pass1_full :
    ttFiber72StateAt 57 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix57 ++ [ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix57 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 57) ttFiber72State57_in_pass1_prefix57

theorem ttFiber72State58_in_pass1_prefix58 :
    ttFiber72StateAt 58 ∈ chainClosureStep ttWord ttFiber72Prefix58 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 36 ∈
      chainClosureStep ttWord ttFiber72Prefix57 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix57 = ttFiber72Prefix36 ++ [ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57]
      (chainClosureStep ttWord ttFiber72Prefix36 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 36) ttFiber72State36_in_pass1_prefix36
  rw [show ttFiber72Prefix58 = ttFiber72Prefix57 ++ [ttFiber72StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 58) []
    (chainClosureStep ttWord ttFiber72Prefix57 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 36) hparentBefore ttFiber72ReverseSingleStep58

theorem ttFiber72State58_in_pass1_full :
    ttFiber72StateAt 58 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix58 ++ [ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix58 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 58) ttFiber72State58_in_pass1_prefix58

theorem ttFiber72State59_in_pass1_prefix59 :
    ttFiber72StateAt 59 ∈ chainClosureStep ttWord ttFiber72Prefix59 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 37 ∈
      chainClosureStep ttWord ttFiber72Prefix58 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix58 = ttFiber72Prefix37 ++ [ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58]
      (chainClosureStep ttWord ttFiber72Prefix37 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 37) ttFiber72State37_in_pass1_prefix37
  rw [show ttFiber72Prefix59 = ttFiber72Prefix58 ++ [ttFiber72StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 59) []
    (chainClosureStep ttWord ttFiber72Prefix58 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 37) hparentBefore ttFiber72ReverseSingleStep59

theorem ttFiber72State59_in_pass1_full :
    ttFiber72StateAt 59 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix59 ++ [ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix59 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 59) ttFiber72State59_in_pass1_prefix59

theorem ttFiber72State60_in_pass1_prefix60 :
    ttFiber72StateAt 60 ∈ chainClosureStep ttWord ttFiber72Prefix60 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 32 ∈
      chainClosureStep ttWord ttFiber72Prefix59 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix59 = ttFiber72Prefix32 ++ [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59]
      (chainClosureStep ttWord ttFiber72Prefix32 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 32) ttFiber72State32_in_pass1_prefix32
  rw [show ttFiber72Prefix60 = ttFiber72Prefix59 ++ [ttFiber72StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 60) []
    (chainClosureStep ttWord ttFiber72Prefix59 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 32) hparentBefore ttFiber72ReverseSingleStep60

theorem ttFiber72State60_in_pass1_full :
    ttFiber72StateAt 60 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix60 ++ [ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix60 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 60) ttFiber72State60_in_pass1_prefix60

theorem ttFiber72State61_in_pass1_prefix61 :
    ttFiber72StateAt 61 ∈ chainClosureStep ttWord ttFiber72Prefix61 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 33 ∈
      chainClosureStep ttWord ttFiber72Prefix60 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix60 = ttFiber72Prefix33 ++ [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60]
      (chainClosureStep ttWord ttFiber72Prefix33 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 33) ttFiber72State33_in_pass1_prefix33
  rw [show ttFiber72Prefix61 = ttFiber72Prefix60 ++ [ttFiber72StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 61) []
    (chainClosureStep ttWord ttFiber72Prefix60 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 33) hparentBefore ttFiber72ReverseSingleStep61

theorem ttFiber72State61_in_pass1_full :
    ttFiber72StateAt 61 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix61 ++ [ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix61 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 61) ttFiber72State61_in_pass1_prefix61

theorem ttFiber72State62_in_pass1_prefix62 :
    ttFiber72StateAt 62 ∈ chainClosureStep ttWord ttFiber72Prefix62 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 34 ∈
      chainClosureStep ttWord ttFiber72Prefix61 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix61 = ttFiber72Prefix34 ++ [ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61]
      (chainClosureStep ttWord ttFiber72Prefix34 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 34) ttFiber72State34_in_pass1_prefix34
  rw [show ttFiber72Prefix62 = ttFiber72Prefix61 ++ [ttFiber72StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 62) []
    (chainClosureStep ttWord ttFiber72Prefix61 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 34) hparentBefore ttFiber72ReverseSingleStep62

theorem ttFiber72State62_in_pass1_full :
    ttFiber72StateAt 62 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix62 ++ [ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix62 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 62) ttFiber72State62_in_pass1_prefix62

theorem ttFiber72State63_in_pass1_prefix63 :
    ttFiber72StateAt 63 ∈ chainClosureStep ttWord ttFiber72Prefix63 ([ttFiber72StateAt 0]) := by
  have hparentBefore : ttFiber72StateAt 35 ∈
      chainClosureStep ttWord ttFiber72Prefix62 ([ttFiber72StateAt 0]) := by
    rw [show ttFiber72Prefix62 = ttFiber72Prefix35 ++ [ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62]
      (chainClosureStep ttWord ttFiber72Prefix35 ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 35) ttFiber72State35_in_pass1_prefix35
  rw [show ttFiber72Prefix63 = ttFiber72Prefix62 ++ [ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 63) []
    (chainClosureStep ttWord ttFiber72Prefix62 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 35) hparentBefore ttFiber72ReverseSingleStep63

theorem ttFiber72State63_in_pass1_full :
    ttFiber72StateAt 63 ∈ chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber72Prefix63 ([ttFiber72StateAt 0]))
    (ttFiber72StateAt 63) ttFiber72State63_in_pass1_prefix63

theorem ttFiber72State5_in_pass2_prefix5 :
    ttFiber72StateAt 5 ∈ chainClosureStep ttWord ttFiber72Prefix5 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
  have hparentBefore : ttFiber72StateAt 7 ∈
      chainClosureStep ttWord ttFiber72Prefix4 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber72Prefix4
      (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0]))
      (ttFiber72StateAt 7) ttFiber72State7_in_pass1_full
  rw [show ttFiber72Prefix5 = ttFiber72Prefix4 ++ [ttFiber72StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 5) []
    (chainClosureStep ttWord ttFiber72Prefix4 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])))
    (ttFiber72StateAt 7) hparentBefore ttFiber72ReverseSingleStep5

theorem ttFiber72State5_in_pass2_full :
    ttFiber72StateAt 5 ∈ chainClosureStep ttWord ttFiber72DirectStates (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix5 ++ [ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12, ttFiber72StateAt 13, ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix5 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])))
    (ttFiber72StateAt 5) ttFiber72State5_in_pass2_prefix5

theorem ttFiber72State13_in_pass2_prefix13 :
    ttFiber72StateAt 13 ∈ chainClosureStep ttWord ttFiber72Prefix13 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
  have hparentBefore : ttFiber72StateAt 5 ∈
      chainClosureStep ttWord ttFiber72Prefix12 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
    rw [show ttFiber72Prefix12 = ttFiber72Prefix5 ++ [ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 6, ttFiber72StateAt 7, ttFiber72StateAt 8, ttFiber72StateAt 9, ttFiber72StateAt 10, ttFiber72StateAt 11, ttFiber72StateAt 12]
      (chainClosureStep ttWord ttFiber72Prefix5 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])))
      (ttFiber72StateAt 5) ttFiber72State5_in_pass2_prefix5
  rw [show ttFiber72Prefix13 = ttFiber72Prefix12 ++ [ttFiber72StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber72StateAt 13) []
    (chainClosureStep ttWord ttFiber72Prefix12 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])))
    (ttFiber72StateAt 5) hparentBefore ttFiber72ReverseSingleStep13

theorem ttFiber72State13_in_pass2_full :
    ttFiber72StateAt 13 ∈ chainClosureStep ttWord ttFiber72DirectStates (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])) := by
  rw [show ttFiber72DirectStates = ttFiber72Prefix13 ++ [ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber72StateAt 14, ttFiber72StateAt 15, ttFiber72StateAt 16, ttFiber72StateAt 17, ttFiber72StateAt 18, ttFiber72StateAt 19, ttFiber72StateAt 20, ttFiber72StateAt 21, ttFiber72StateAt 22, ttFiber72StateAt 23, ttFiber72StateAt 24, ttFiber72StateAt 25, ttFiber72StateAt 26, ttFiber72StateAt 27, ttFiber72StateAt 28, ttFiber72StateAt 29, ttFiber72StateAt 30, ttFiber72StateAt 31, ttFiber72StateAt 32, ttFiber72StateAt 33, ttFiber72StateAt 34, ttFiber72StateAt 35, ttFiber72StateAt 36, ttFiber72StateAt 37, ttFiber72StateAt 38, ttFiber72StateAt 39, ttFiber72StateAt 40, ttFiber72StateAt 41, ttFiber72StateAt 42, ttFiber72StateAt 43, ttFiber72StateAt 44, ttFiber72StateAt 45, ttFiber72StateAt 46, ttFiber72StateAt 47, ttFiber72StateAt 48, ttFiber72StateAt 49, ttFiber72StateAt 50, ttFiber72StateAt 51, ttFiber72StateAt 52, ttFiber72StateAt 53, ttFiber72StateAt 54, ttFiber72StateAt 55, ttFiber72StateAt 56, ttFiber72StateAt 57, ttFiber72StateAt 58, ttFiber72StateAt 59, ttFiber72StateAt 60, ttFiber72StateAt 61, ttFiber72StateAt 62, ttFiber72StateAt 63]
    (chainClosureStep ttWord ttFiber72Prefix13 (chainClosureStep ttWord ttFiber72DirectStates ([ttFiber72StateAt 0])))
    (ttFiber72StateAt 13) ttFiber72State13_in_pass2_prefix13

theorem ttFiber72State0_in_close :
    ttFiber72StateAt 0 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber72DirectStates ttFiber72DirectStates.length
    [ttFiber72StateAt 0] (ttFiber72StateAt 0) (by simp)

theorem ttFiber72State1_in_close :
    ttFiber72StateAt 1 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 1 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 1) ttFiber72State1_in_pass1_full

theorem ttFiber72State2_in_close :
    ttFiber72StateAt 2 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 2 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 2) ttFiber72State2_in_pass1_full

theorem ttFiber72State3_in_close :
    ttFiber72StateAt 3 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 3 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 3) ttFiber72State3_in_pass1_full

theorem ttFiber72State4_in_close :
    ttFiber72StateAt 4 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 4 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 4) ttFiber72State4_in_pass1_full

theorem ttFiber72State5_in_close :
    ttFiber72StateAt 5 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 5 ∈ closeChainFiber ttWord ttFiber72DirectStates (62 + 2)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber72DirectStates 62
    [ttFiber72StateAt 0] (ttFiber72StateAt 5) ttFiber72FirstPassGrows
    ttFiber72State5_in_pass2_full

theorem ttFiber72State6_in_close :
    ttFiber72StateAt 6 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 6 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 6) ttFiber72State6_in_pass1_full

theorem ttFiber72State7_in_close :
    ttFiber72StateAt 7 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 7 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 7) ttFiber72State7_in_pass1_full

theorem ttFiber72State8_in_close :
    ttFiber72StateAt 8 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 8 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 8) ttFiber72State8_in_pass1_full

theorem ttFiber72State9_in_close :
    ttFiber72StateAt 9 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 9 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 9) ttFiber72State9_in_pass1_full

theorem ttFiber72State10_in_close :
    ttFiber72StateAt 10 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 10 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 10) ttFiber72State10_in_pass1_full

theorem ttFiber72State11_in_close :
    ttFiber72StateAt 11 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 11 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 11) ttFiber72State11_in_pass1_full

theorem ttFiber72State12_in_close :
    ttFiber72StateAt 12 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 12 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 12) ttFiber72State12_in_pass1_full

theorem ttFiber72State13_in_close :
    ttFiber72StateAt 13 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 13 ∈ closeChainFiber ttWord ttFiber72DirectStates (62 + 2)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber72DirectStates 62
    [ttFiber72StateAt 0] (ttFiber72StateAt 13) ttFiber72FirstPassGrows
    ttFiber72State13_in_pass2_full

theorem ttFiber72State14_in_close :
    ttFiber72StateAt 14 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 14 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 14) ttFiber72State14_in_pass1_full

theorem ttFiber72State15_in_close :
    ttFiber72StateAt 15 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 15 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 15) ttFiber72State15_in_pass1_full

theorem ttFiber72State16_in_close :
    ttFiber72StateAt 16 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 16 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 16) ttFiber72State16_in_pass1_full

theorem ttFiber72State17_in_close :
    ttFiber72StateAt 17 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 17 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 17) ttFiber72State17_in_pass1_full

theorem ttFiber72State18_in_close :
    ttFiber72StateAt 18 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 18 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 18) ttFiber72State18_in_pass1_full

theorem ttFiber72State19_in_close :
    ttFiber72StateAt 19 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 19 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 19) ttFiber72State19_in_pass1_full

theorem ttFiber72State20_in_close :
    ttFiber72StateAt 20 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 20 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 20) ttFiber72State20_in_pass1_full

theorem ttFiber72State21_in_close :
    ttFiber72StateAt 21 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 21 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 21) ttFiber72State21_in_pass1_full

theorem ttFiber72State22_in_close :
    ttFiber72StateAt 22 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 22 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 22) ttFiber72State22_in_pass1_full

theorem ttFiber72State23_in_close :
    ttFiber72StateAt 23 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 23 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 23) ttFiber72State23_in_pass1_full

theorem ttFiber72State24_in_close :
    ttFiber72StateAt 24 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 24 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 24) ttFiber72State24_in_pass1_full

theorem ttFiber72State25_in_close :
    ttFiber72StateAt 25 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 25 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 25) ttFiber72State25_in_pass1_full

theorem ttFiber72State26_in_close :
    ttFiber72StateAt 26 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 26 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 26) ttFiber72State26_in_pass1_full

theorem ttFiber72State27_in_close :
    ttFiber72StateAt 27 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 27 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 27) ttFiber72State27_in_pass1_full

theorem ttFiber72State28_in_close :
    ttFiber72StateAt 28 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 28 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 28) ttFiber72State28_in_pass1_full

theorem ttFiber72State29_in_close :
    ttFiber72StateAt 29 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 29 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 29) ttFiber72State29_in_pass1_full

theorem ttFiber72State30_in_close :
    ttFiber72StateAt 30 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 30 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 30) ttFiber72State30_in_pass1_full

theorem ttFiber72State31_in_close :
    ttFiber72StateAt 31 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 31 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 31) ttFiber72State31_in_pass1_full

theorem ttFiber72State32_in_close :
    ttFiber72StateAt 32 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 32 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 32) ttFiber72State32_in_pass1_full

theorem ttFiber72State33_in_close :
    ttFiber72StateAt 33 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 33 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 33) ttFiber72State33_in_pass1_full

theorem ttFiber72State34_in_close :
    ttFiber72StateAt 34 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 34 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 34) ttFiber72State34_in_pass1_full

theorem ttFiber72State35_in_close :
    ttFiber72StateAt 35 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 35 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 35) ttFiber72State35_in_pass1_full

theorem ttFiber72State36_in_close :
    ttFiber72StateAt 36 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 36 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 36) ttFiber72State36_in_pass1_full

theorem ttFiber72State37_in_close :
    ttFiber72StateAt 37 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 37 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 37) ttFiber72State37_in_pass1_full

theorem ttFiber72State38_in_close :
    ttFiber72StateAt 38 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 38 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 38) ttFiber72State38_in_pass1_full

theorem ttFiber72State39_in_close :
    ttFiber72StateAt 39 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 39 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 39) ttFiber72State39_in_pass1_full

theorem ttFiber72State40_in_close :
    ttFiber72StateAt 40 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 40 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 40) ttFiber72State40_in_pass1_full

theorem ttFiber72State41_in_close :
    ttFiber72StateAt 41 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 41 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 41) ttFiber72State41_in_pass1_full

theorem ttFiber72State42_in_close :
    ttFiber72StateAt 42 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 42 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 42) ttFiber72State42_in_pass1_full

theorem ttFiber72State43_in_close :
    ttFiber72StateAt 43 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 43 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 43) ttFiber72State43_in_pass1_full

theorem ttFiber72State44_in_close :
    ttFiber72StateAt 44 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 44 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 44) ttFiber72State44_in_pass1_full

theorem ttFiber72State45_in_close :
    ttFiber72StateAt 45 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 45 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 45) ttFiber72State45_in_pass1_full

theorem ttFiber72State46_in_close :
    ttFiber72StateAt 46 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 46 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 46) ttFiber72State46_in_pass1_full

theorem ttFiber72State47_in_close :
    ttFiber72StateAt 47 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 47 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 47) ttFiber72State47_in_pass1_full

theorem ttFiber72State48_in_close :
    ttFiber72StateAt 48 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 48 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 48) ttFiber72State48_in_pass1_full

theorem ttFiber72State49_in_close :
    ttFiber72StateAt 49 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 49 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 49) ttFiber72State49_in_pass1_full

theorem ttFiber72State50_in_close :
    ttFiber72StateAt 50 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 50 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 50) ttFiber72State50_in_pass1_full

theorem ttFiber72State51_in_close :
    ttFiber72StateAt 51 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 51 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 51) ttFiber72State51_in_pass1_full

theorem ttFiber72State52_in_close :
    ttFiber72StateAt 52 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 52 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 52) ttFiber72State52_in_pass1_full

theorem ttFiber72State53_in_close :
    ttFiber72StateAt 53 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 53 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 53) ttFiber72State53_in_pass1_full

theorem ttFiber72State54_in_close :
    ttFiber72StateAt 54 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 54 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 54) ttFiber72State54_in_pass1_full

theorem ttFiber72State55_in_close :
    ttFiber72StateAt 55 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 55 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 55) ttFiber72State55_in_pass1_full

theorem ttFiber72State56_in_close :
    ttFiber72StateAt 56 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 56 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 56) ttFiber72State56_in_pass1_full

theorem ttFiber72State57_in_close :
    ttFiber72StateAt 57 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 57 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 57) ttFiber72State57_in_pass1_full

theorem ttFiber72State58_in_close :
    ttFiber72StateAt 58 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 58 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 58) ttFiber72State58_in_pass1_full

theorem ttFiber72State59_in_close :
    ttFiber72StateAt 59 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 59 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 59) ttFiber72State59_in_pass1_full

theorem ttFiber72State60_in_close :
    ttFiber72StateAt 60 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 60 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 60) ttFiber72State60_in_pass1_full

theorem ttFiber72State61_in_close :
    ttFiber72StateAt 61 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 61 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 61) ttFiber72State61_in_pass1_full

theorem ttFiber72State62_in_close :
    ttFiber72StateAt 62 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 62 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 62) ttFiber72State62_in_pass1_full

theorem ttFiber72State63_in_close :
    ttFiber72StateAt 63 ∈
      closeChainFiber ttWord ttFiber72DirectStates ttFiber72DirectStates.length
        [ttFiber72StateAt 0] := by
  change ttFiber72StateAt 63 ∈ closeChainFiber ttWord ttFiber72DirectStates (63 + 1)
    [ttFiber72StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber72DirectStates 63
    [ttFiber72StateAt 0] (ttFiber72StateAt 63) ttFiber72State63_in_pass1_full

theorem ttFiber72DirectConnected :
    chainFiberConnected ttWord ttFiber72DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber72DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber72State0_in_close
  · subst state
    exact ttFiber72State1_in_close
  · subst state
    exact ttFiber72State2_in_close
  · subst state
    exact ttFiber72State3_in_close
  · subst state
    exact ttFiber72State4_in_close
  · subst state
    exact ttFiber72State5_in_close
  · subst state
    exact ttFiber72State6_in_close
  · subst state
    exact ttFiber72State7_in_close
  · subst state
    exact ttFiber72State8_in_close
  · subst state
    exact ttFiber72State9_in_close
  · subst state
    exact ttFiber72State10_in_close
  · subst state
    exact ttFiber72State11_in_close
  · subst state
    exact ttFiber72State12_in_close
  · subst state
    exact ttFiber72State13_in_close
  · subst state
    exact ttFiber72State14_in_close
  · subst state
    exact ttFiber72State15_in_close
  · subst state
    exact ttFiber72State16_in_close
  · subst state
    exact ttFiber72State17_in_close
  · subst state
    exact ttFiber72State18_in_close
  · subst state
    exact ttFiber72State19_in_close
  · subst state
    exact ttFiber72State20_in_close
  · subst state
    exact ttFiber72State21_in_close
  · subst state
    exact ttFiber72State22_in_close
  · subst state
    exact ttFiber72State23_in_close
  · subst state
    exact ttFiber72State24_in_close
  · subst state
    exact ttFiber72State25_in_close
  · subst state
    exact ttFiber72State26_in_close
  · subst state
    exact ttFiber72State27_in_close
  · subst state
    exact ttFiber72State28_in_close
  · subst state
    exact ttFiber72State29_in_close
  · subst state
    exact ttFiber72State30_in_close
  · subst state
    exact ttFiber72State31_in_close
  · subst state
    exact ttFiber72State32_in_close
  · subst state
    exact ttFiber72State33_in_close
  · subst state
    exact ttFiber72State34_in_close
  · subst state
    exact ttFiber72State35_in_close
  · subst state
    exact ttFiber72State36_in_close
  · subst state
    exact ttFiber72State37_in_close
  · subst state
    exact ttFiber72State38_in_close
  · subst state
    exact ttFiber72State39_in_close
  · subst state
    exact ttFiber72State40_in_close
  · subst state
    exact ttFiber72State41_in_close
  · subst state
    exact ttFiber72State42_in_close
  · subst state
    exact ttFiber72State43_in_close
  · subst state
    exact ttFiber72State44_in_close
  · subst state
    exact ttFiber72State45_in_close
  · subst state
    exact ttFiber72State46_in_close
  · subst state
    exact ttFiber72State47_in_close
  · subst state
    exact ttFiber72State48_in_close
  · subst state
    exact ttFiber72State49_in_close
  · subst state
    exact ttFiber72State50_in_close
  · subst state
    exact ttFiber72State51_in_close
  · subst state
    exact ttFiber72State52_in_close
  · subst state
    exact ttFiber72State53_in_close
  · subst state
    exact ttFiber72State54_in_close
  · subst state
    exact ttFiber72State55_in_close
  · subst state
    exact ttFiber72State56_in_close
  · subst state
    exact ttFiber72State57_in_close
  · subst state
    exact ttFiber72State58_in_close
  · subst state
    exact ttFiber72State59_in_close
  · subst state
    exact ttFiber72State60_in_close
  · subst state
    exact ttFiber72State61_in_close
  · subst state
    exact ttFiber72State62_in_close
  · subst state
    exact ttFiber72State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
