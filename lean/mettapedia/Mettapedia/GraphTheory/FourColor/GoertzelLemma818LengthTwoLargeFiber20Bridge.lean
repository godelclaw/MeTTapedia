import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber20

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber20StateAt (i : Nat) : List TauState :=
  directStates (ttFiber20RowAt i).sourceLeft (ttFiber20RowAt i).sourceRight

def ttFiber20DirectStates : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]

def ttFiber20Prefix0 : List (List TauState) :=
  [ttFiber20StateAt 0]

def ttFiber20Prefix1 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1]

def ttFiber20Prefix2 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2]

def ttFiber20Prefix3 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3]

def ttFiber20Prefix4 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4]

def ttFiber20Prefix5 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5]

def ttFiber20Prefix6 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6]

def ttFiber20Prefix7 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7]

def ttFiber20Prefix8 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8]

def ttFiber20Prefix9 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9]

def ttFiber20Prefix10 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10]

def ttFiber20Prefix11 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11]

def ttFiber20Prefix12 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12]

def ttFiber20Prefix13 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13]

def ttFiber20Prefix14 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14]

def ttFiber20Prefix15 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15]

def ttFiber20Prefix16 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16]

def ttFiber20Prefix17 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17]

def ttFiber20Prefix18 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18]

def ttFiber20Prefix19 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19]

def ttFiber20Prefix20 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20]

def ttFiber20Prefix21 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21]

def ttFiber20Prefix22 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22]

def ttFiber20Prefix23 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23]

def ttFiber20Prefix24 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24]

def ttFiber20Prefix25 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25]

def ttFiber20Prefix26 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26]

def ttFiber20Prefix27 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27]

def ttFiber20Prefix28 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28]

def ttFiber20Prefix29 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29]

def ttFiber20Prefix30 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30]

def ttFiber20Prefix31 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31]

def ttFiber20Prefix32 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32]

def ttFiber20Prefix33 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33]

def ttFiber20Prefix34 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34]

def ttFiber20Prefix35 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35]

def ttFiber20Prefix36 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36]

def ttFiber20Prefix37 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37]

def ttFiber20Prefix38 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38]

def ttFiber20Prefix39 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39]

def ttFiber20Prefix40 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40]

def ttFiber20Prefix41 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41]

def ttFiber20Prefix42 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42]

def ttFiber20Prefix43 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43]

def ttFiber20Prefix44 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44]

def ttFiber20Prefix45 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45]

def ttFiber20Prefix46 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46]

def ttFiber20Prefix47 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47]

def ttFiber20Prefix48 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48]

def ttFiber20Prefix49 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49]

def ttFiber20Prefix50 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50]

def ttFiber20Prefix51 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51]

def ttFiber20Prefix52 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52]

def ttFiber20Prefix53 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53]

def ttFiber20Prefix54 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54]

def ttFiber20Prefix55 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55]

def ttFiber20Prefix56 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56]

def ttFiber20Prefix57 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57]

def ttFiber20Prefix58 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58]

def ttFiber20Prefix59 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59]

def ttFiber20Prefix60 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60]

def ttFiber20Prefix61 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61]

def ttFiber20Prefix62 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62]

def ttFiber20Prefix63 : List (List TauState) :=
  [ttFiber20StateAt 0, ttFiber20StateAt 1, ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]

theorem ttFiber20ReverseRow_1_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk0] at h
  exact h.2

theorem ttFiber20ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 1)
      (ttFiber20RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 1) (by decide) ttFiber20ReverseRow_1_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_2_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk1] at h
  exact h.1

theorem ttFiber20ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 2)
      (ttFiber20RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 2) (by decide) ttFiber20ReverseRow_2_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_3_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk1] at h
  exact h.2

theorem ttFiber20ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 3)
      (ttFiber20RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 3) (by decide) ttFiber20ReverseRow_3_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_4_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk2] at h
  exact h.1

theorem ttFiber20ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 4)
      (ttFiber20RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 4) (by decide) ttFiber20ReverseRow_4_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_5_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk2] at h
  exact h.2

theorem ttFiber20ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 5)
      (ttFiber20RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 5) (by decide) ttFiber20ReverseRow_5_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_6_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk3] at h
  exact h.1

theorem ttFiber20ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 6)
      (ttFiber20RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 6) (by decide) ttFiber20ReverseRow_6_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_7_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk3] at h
  exact h.2

theorem ttFiber20ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 7)
      (ttFiber20RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 7) (by decide) ttFiber20ReverseRow_7_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_8_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk4] at h
  exact h.1

theorem ttFiber20ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 8)
      (ttFiber20RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 8) (by decide) ttFiber20ReverseRow_8_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_9_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk4] at h
  exact h.2

theorem ttFiber20ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 9)
      (ttFiber20RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 9) (by decide) ttFiber20ReverseRow_9_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_10_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk5] at h
  exact h.1

theorem ttFiber20ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 10)
      (ttFiber20RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 10) (by decide) ttFiber20ReverseRow_10_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_11_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk5] at h
  exact h.2

theorem ttFiber20ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 11)
      (ttFiber20RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 11) (by decide) ttFiber20ReverseRow_11_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_12_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk6] at h
  exact h.1

theorem ttFiber20ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 12)
      (ttFiber20RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 12) (by decide) ttFiber20ReverseRow_12_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_13_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk6] at h
  exact h.2

theorem ttFiber20ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 13)
      (ttFiber20RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 13) (by decide) ttFiber20ReverseRow_13_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_14_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk7] at h
  exact h.1

theorem ttFiber20ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 6) (ttFiber20StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 6) (ttFiber20StateAt 14)
      (ttFiber20RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 14) (by decide) ttFiber20ReverseRow_14_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_15_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk7] at h
  exact h.2

theorem ttFiber20ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 7) (ttFiber20StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 7) (ttFiber20StateAt 15)
      (ttFiber20RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 15) (by decide) ttFiber20ReverseRow_15_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_16_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk8] at h
  exact h.1

theorem ttFiber20ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 20) (ttFiber20StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 20) (ttFiber20StateAt 16)
      (ttFiber20RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 16) (by decide) ttFiber20ReverseRow_16_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_17_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk8] at h
  exact h.2

theorem ttFiber20ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 21) (ttFiber20StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 21) (ttFiber20StateAt 17)
      (ttFiber20RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 17) (by decide) ttFiber20ReverseRow_17_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_18_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk9] at h
  exact h.1

theorem ttFiber20ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 12) (ttFiber20StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 12) (ttFiber20StateAt 18)
      (ttFiber20RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 18) (by decide) ttFiber20ReverseRow_18_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_19_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk9] at h
  exact h.2

theorem ttFiber20ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 13) (ttFiber20StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 13) (ttFiber20StateAt 19)
      (ttFiber20RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 19) (by decide) ttFiber20ReverseRow_19_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_20_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk10] at h
  exact h.1

theorem ttFiber20ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 8) (ttFiber20StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 8) (ttFiber20StateAt 20)
      (ttFiber20RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 20) (by decide) ttFiber20ReverseRow_20_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_21_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk10] at h
  exact h.2

theorem ttFiber20ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 9) (ttFiber20StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 9) (ttFiber20StateAt 21)
      (ttFiber20RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 21) (by decide) ttFiber20ReverseRow_21_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_22_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk11] at h
  exact h.1

theorem ttFiber20ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 10) (ttFiber20StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 10) (ttFiber20StateAt 22)
      (ttFiber20RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 22) (by decide) ttFiber20ReverseRow_22_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_23_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk11] at h
  exact h.2

theorem ttFiber20ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 11) (ttFiber20StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 11) (ttFiber20StateAt 23)
      (ttFiber20RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 23) (by decide) ttFiber20ReverseRow_23_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_24_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk12] at h
  exact h.1

theorem ttFiber20ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 28) (ttFiber20StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 28) (ttFiber20StateAt 24)
      (ttFiber20RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 24) (by decide) ttFiber20ReverseRow_24_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_25_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk12] at h
  exact h.2

theorem ttFiber20ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 29) (ttFiber20StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 29) (ttFiber20StateAt 25)
      (ttFiber20RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 25) (by decide) ttFiber20ReverseRow_25_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_26_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk13] at h
  exact h.1

theorem ttFiber20ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 26)
      (ttFiber20RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 26) (by decide) ttFiber20ReverseRow_26_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_27_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk13] at h
  exact h.2

theorem ttFiber20ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 27)
      (ttFiber20RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 27) (by decide) ttFiber20ReverseRow_27_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_28_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk14] at h
  exact h.1

theorem ttFiber20ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 28)
      (ttFiber20RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 28) (by decide) ttFiber20ReverseRow_28_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_29_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk14] at h
  exact h.2

theorem ttFiber20ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 29)
      (ttFiber20RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 29) (by decide) ttFiber20ReverseRow_29_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_30_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk15] at h
  exact h.1

theorem ttFiber20ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 30)
      (ttFiber20RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 30) (by decide) ttFiber20ReverseRow_30_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_31_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk15] at h
  exact h.2

theorem ttFiber20ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 31)
      (ttFiber20RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 31) (by decide) ttFiber20ReverseRow_31_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_32_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk16] at h
  exact h.1

theorem ttFiber20ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 0) (ttFiber20StateAt 32)
      (ttFiber20RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 32) (by decide) ttFiber20ReverseRow_32_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_33_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk16] at h
  exact h.2

theorem ttFiber20ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 1) (ttFiber20StateAt 33)
      (ttFiber20RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 33) (by decide) ttFiber20ReverseRow_33_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_34_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk17] at h
  exact h.1

theorem ttFiber20ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 2) (ttFiber20StateAt 34)
      (ttFiber20RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 34) (by decide) ttFiber20ReverseRow_34_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_35_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk17] at h
  exact h.2

theorem ttFiber20ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 3) (ttFiber20StateAt 35)
      (ttFiber20RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 35) (by decide) ttFiber20ReverseRow_35_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_36_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk18] at h
  exact h.1

theorem ttFiber20ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 4) (ttFiber20StateAt 36)
      (ttFiber20RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 36) (by decide) ttFiber20ReverseRow_36_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_37_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk18] at h
  exact h.2

theorem ttFiber20ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 5) (ttFiber20StateAt 37)
      (ttFiber20RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 37) (by decide) ttFiber20ReverseRow_37_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_38_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk19] at h
  exact h.1

theorem ttFiber20ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 6) (ttFiber20StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 6) (ttFiber20StateAt 38)
      (ttFiber20RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 38) (by decide) ttFiber20ReverseRow_38_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_39_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk19] at h
  exact h.2

theorem ttFiber20ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 7) (ttFiber20StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 7) (ttFiber20StateAt 39)
      (ttFiber20RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 39) (by decide) ttFiber20ReverseRow_39_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_40_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk20] at h
  exact h.1

theorem ttFiber20ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 8) (ttFiber20StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 8) (ttFiber20StateAt 40)
      (ttFiber20RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 40) (by decide) ttFiber20ReverseRow_40_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_41_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk20] at h
  exact h.2

theorem ttFiber20ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 9) (ttFiber20StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 9) (ttFiber20StateAt 41)
      (ttFiber20RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 41) (by decide) ttFiber20ReverseRow_41_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_42_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk21] at h
  exact h.1

theorem ttFiber20ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 10) (ttFiber20StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 10) (ttFiber20StateAt 42)
      (ttFiber20RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 42) (by decide) ttFiber20ReverseRow_42_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_43_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk21] at h
  exact h.2

theorem ttFiber20ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 11) (ttFiber20StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 11) (ttFiber20StateAt 43)
      (ttFiber20RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 43) (by decide) ttFiber20ReverseRow_43_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_44_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk22] at h
  exact h.1

theorem ttFiber20ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 12) (ttFiber20StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 12) (ttFiber20StateAt 44)
      (ttFiber20RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 44) (by decide) ttFiber20ReverseRow_44_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_45_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk22] at h
  exact h.2

theorem ttFiber20ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 13) (ttFiber20StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 13) (ttFiber20StateAt 45)
      (ttFiber20RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 45) (by decide) ttFiber20ReverseRow_45_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_46_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk23] at h
  exact h.1

theorem ttFiber20ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 14) (ttFiber20StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 14) (ttFiber20StateAt 46)
      (ttFiber20RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 46) (by decide) ttFiber20ReverseRow_46_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_47_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk23] at h
  exact h.2

theorem ttFiber20ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 15) (ttFiber20StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 15) (ttFiber20StateAt 47)
      (ttFiber20RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 47) (by decide) ttFiber20ReverseRow_47_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_48_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk24] at h
  exact h.1

theorem ttFiber20ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 32) (ttFiber20StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 32) (ttFiber20StateAt 48)
      (ttFiber20RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 48) (by decide) ttFiber20ReverseRow_48_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_49_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk24] at h
  exact h.2

theorem ttFiber20ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 33) (ttFiber20StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 33) (ttFiber20StateAt 49)
      (ttFiber20RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 49) (by decide) ttFiber20ReverseRow_49_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_50_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk25] at h
  exact h.1

theorem ttFiber20ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 48) (ttFiber20StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 48) (ttFiber20StateAt 50)
      (ttFiber20RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 50) (by decide) ttFiber20ReverseRow_50_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_51_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk25] at h
  exact h.2

theorem ttFiber20ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 35) (ttFiber20StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 35) (ttFiber20StateAt 51)
      (ttFiber20RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 51) (by decide) ttFiber20ReverseRow_51_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_52_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk26] at h
  exact h.1

theorem ttFiber20ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 36) (ttFiber20StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 36) (ttFiber20StateAt 52)
      (ttFiber20RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 52) (by decide) ttFiber20ReverseRow_52_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_53_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk26] at h
  exact h.2

theorem ttFiber20ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 37) (ttFiber20StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 37) (ttFiber20StateAt 53)
      (ttFiber20RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 53) (by decide) ttFiber20ReverseRow_53_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_54_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk27] at h
  exact h.1

theorem ttFiber20ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 49) (ttFiber20StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 49) (ttFiber20StateAt 54)
      (ttFiber20RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 54) (by decide) ttFiber20ReverseRow_54_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_55_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk27] at h
  exact h.2

theorem ttFiber20ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 48) (ttFiber20StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 48) (ttFiber20StateAt 55)
      (ttFiber20RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 55) (by decide) ttFiber20ReverseRow_55_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_56_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk28] at h
  exact h.1

theorem ttFiber20ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 40) (ttFiber20StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 40) (ttFiber20StateAt 56)
      (ttFiber20RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 56) (by decide) ttFiber20ReverseRow_56_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_57_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk28] at h
  exact h.2

theorem ttFiber20ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 41) (ttFiber20StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 41) (ttFiber20StateAt 57)
      (ttFiber20RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 57) (by decide) ttFiber20ReverseRow_57_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_58_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk29] at h
  exact h.1

theorem ttFiber20ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 26) (ttFiber20StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 26) (ttFiber20StateAt 58)
      (ttFiber20RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 58) (by decide) ttFiber20ReverseRow_58_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_59_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk29] at h
  exact h.2

theorem ttFiber20ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 27) (ttFiber20StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 27) (ttFiber20StateAt 59)
      (ttFiber20RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 59) (by decide) ttFiber20ReverseRow_59_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_60_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk30] at h
  exact h.1

theorem ttFiber20ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 28) (ttFiber20StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 28) (ttFiber20StateAt 60)
      (ttFiber20RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 60) (by decide) ttFiber20ReverseRow_60_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_61_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk30] at h
  exact h.2

theorem ttFiber20ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 29) (ttFiber20StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 29) (ttFiber20StateAt 61)
      (ttFiber20RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 61) (by decide) ttFiber20ReverseRow_61_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_62_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk31] at h
  exact h.1

theorem ttFiber20ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 60) (ttFiber20StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 60) (ttFiber20StateAt 62)
      (ttFiber20RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 62) (by decide) ttFiber20ReverseRow_62_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20ReverseRow_63_ok' :
    directRowReverseValid ttFiber20Key ttFiber20Expected (ttFiber20RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber20Chunk31] at h
  exact h.2

theorem ttFiber20ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber20StateAt 31) (ttFiber20StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber20StateAt 31) (ttFiber20StateAt 63)
      (ttFiber20RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber20Key ttFiber20Expected
      (ttFiber20RowAt 63) (by decide) ttFiber20ReverseRow_63_ok'
    simpa [ttFiber20StateAt, ttFiber20RowAt, ttFiber20Rows, listGetD, directRow] using h

theorem ttFiber20FirstPassGrows :
    ((chainClosureStep ttWord ttFiber20DirectStates [ttFiber20StateAt 0]).length ==
      [ttFiber20StateAt 0].length) = false := by
  have hroot : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20DirectStates [ttFiber20StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber20DirectStates [ttFiber20StateAt 0]
      (ttFiber20StateAt 0) (by simp)
  have hnew : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20DirectStates [ttFiber20StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber20DirectStates [ttFiber20StateAt 0]
      (ttFiber20StateAt 0) (ttFiber20StateAt 1) (by decide) (by simp)
      ttFiber20ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber20DirectStates [ttFiber20StateAt 0])
    (ttFiber20StateAt 0) (ttFiber20StateAt 1) hroot hnew (by decide)

theorem ttFiber20State0_in_pass0_full :
    ttFiber20StateAt 0 ∈ [ttFiber20StateAt 0] := by
  simp

theorem ttFiber20State0_in_pass1_full :
    ttFiber20StateAt 0 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber20DirectStates
    ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full

theorem ttFiber20State1_in_pass1_prefix1 :
    ttFiber20StateAt 1 ∈ chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix0 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix0
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix1 = ttFiber20Prefix0 ++ [ttFiber20StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 1) []
    (chainClosureStep ttWord ttFiber20Prefix0 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep1

theorem ttFiber20State1_in_pass1_full :
    ttFiber20StateAt 1 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix1 ++ [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1

theorem ttFiber20State2_in_pass1_prefix2 :
    ttFiber20StateAt 2 ∈ chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix1 = ttFiber20Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1
  rw [show ttFiber20Prefix2 = ttFiber20Prefix1 ++ [ttFiber20StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 2) []
    (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) hparentBefore ttFiber20ReverseSingleStep2

theorem ttFiber20State2_in_pass1_full :
    ttFiber20StateAt 2 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix2 ++ [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 2) ttFiber20State2_in_pass1_prefix2

theorem ttFiber20State3_in_pass1_prefix3 :
    ttFiber20StateAt 3 ∈ chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix2
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix3 = ttFiber20Prefix2 ++ [ttFiber20StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 3) []
    (chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep3

theorem ttFiber20State3_in_pass1_full :
    ttFiber20StateAt 3 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix3 ++ [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 3) ttFiber20State3_in_pass1_prefix3

theorem ttFiber20State4_in_pass1_prefix4 :
    ttFiber20StateAt 4 ∈ chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix3
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix4 = ttFiber20Prefix3 ++ [ttFiber20StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 4) []
    (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep4

theorem ttFiber20State4_in_pass1_full :
    ttFiber20StateAt 4 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix4 ++ [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 4) ttFiber20State4_in_pass1_prefix4

theorem ttFiber20State5_in_pass1_prefix5 :
    ttFiber20StateAt 5 ∈ chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix4 = ttFiber20Prefix1 ++ [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4]
      (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1
  rw [show ttFiber20Prefix5 = ttFiber20Prefix4 ++ [ttFiber20StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 5) []
    (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) hparentBefore ttFiber20ReverseSingleStep5

theorem ttFiber20State5_in_pass1_full :
    ttFiber20StateAt 5 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix5 ++ [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 5) ttFiber20State5_in_pass1_prefix5

theorem ttFiber20State6_in_pass1_prefix6 :
    ttFiber20StateAt 6 ∈ chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 4 ∈
      chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix5 = ttFiber20Prefix4 ++ [ttFiber20StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 5]
      (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 4) ttFiber20State4_in_pass1_prefix4
  rw [show ttFiber20Prefix6 = ttFiber20Prefix5 ++ [ttFiber20StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 6) []
    (chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 4) hparentBefore ttFiber20ReverseSingleStep6

theorem ttFiber20State6_in_pass1_full :
    ttFiber20StateAt 6 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix6 ++ [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 6) ttFiber20State6_in_pass1_prefix6

theorem ttFiber20State7_in_pass1_prefix7 :
    ttFiber20StateAt 7 ∈ chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 3 ∈
      chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix6 = ttFiber20Prefix3 ++ [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6]
      (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 3) ttFiber20State3_in_pass1_prefix3
  rw [show ttFiber20Prefix7 = ttFiber20Prefix6 ++ [ttFiber20StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 7) []
    (chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 3) hparentBefore ttFiber20ReverseSingleStep7

theorem ttFiber20State7_in_pass1_full :
    ttFiber20StateAt 7 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix7 ++ [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 7) ttFiber20State7_in_pass1_prefix7

theorem ttFiber20State8_in_pass1_prefix8 :
    ttFiber20StateAt 8 ∈ chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix7
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix8 = ttFiber20Prefix7 ++ [ttFiber20StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 8) []
    (chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep8

theorem ttFiber20State8_in_pass1_full :
    ttFiber20StateAt 8 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix8 ++ [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 8) ttFiber20State8_in_pass1_prefix8

theorem ttFiber20State9_in_pass1_prefix9 :
    ttFiber20StateAt 9 ∈ chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix8 = ttFiber20Prefix1 ++ [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8]
      (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1
  rw [show ttFiber20Prefix9 = ttFiber20Prefix8 ++ [ttFiber20StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 9) []
    (chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) hparentBefore ttFiber20ReverseSingleStep9

theorem ttFiber20State9_in_pass1_full :
    ttFiber20StateAt 9 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix9 ++ [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 9) ttFiber20State9_in_pass1_prefix9

theorem ttFiber20State10_in_pass1_prefix10 :
    ttFiber20StateAt 10 ∈ chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 2 ∈
      chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix9 = ttFiber20Prefix2 ++ [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9]
      (chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 2) ttFiber20State2_in_pass1_prefix2
  rw [show ttFiber20Prefix10 = ttFiber20Prefix9 ++ [ttFiber20StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 10) []
    (chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 2) hparentBefore ttFiber20ReverseSingleStep10

theorem ttFiber20State10_in_pass1_full :
    ttFiber20StateAt 10 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix10 ++ [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 10) ttFiber20State10_in_pass1_prefix10

theorem ttFiber20State11_in_pass1_prefix11 :
    ttFiber20StateAt 11 ∈ chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 3 ∈
      chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix10 = ttFiber20Prefix3 ++ [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10]
      (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 3) ttFiber20State3_in_pass1_prefix3
  rw [show ttFiber20Prefix11 = ttFiber20Prefix10 ++ [ttFiber20StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 11) []
    (chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 3) hparentBefore ttFiber20ReverseSingleStep11

theorem ttFiber20State11_in_pass1_full :
    ttFiber20StateAt 11 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix11 ++ [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 11) ttFiber20State11_in_pass1_prefix11

theorem ttFiber20State12_in_pass1_prefix12 :
    ttFiber20StateAt 12 ∈ chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 4 ∈
      chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix11 = ttFiber20Prefix4 ++ [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11]
      (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 4) ttFiber20State4_in_pass1_prefix4
  rw [show ttFiber20Prefix12 = ttFiber20Prefix11 ++ [ttFiber20StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 12) []
    (chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 4) hparentBefore ttFiber20ReverseSingleStep12

theorem ttFiber20State12_in_pass1_full :
    ttFiber20StateAt 12 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix12 ++ [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 12) ttFiber20State12_in_pass1_prefix12

theorem ttFiber20State13_in_pass1_prefix13 :
    ttFiber20StateAt 13 ∈ chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 5 ∈
      chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix12 = ttFiber20Prefix5 ++ [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12]
      (chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 5) ttFiber20State5_in_pass1_prefix5
  rw [show ttFiber20Prefix13 = ttFiber20Prefix12 ++ [ttFiber20StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 13) []
    (chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 5) hparentBefore ttFiber20ReverseSingleStep13

theorem ttFiber20State13_in_pass1_full :
    ttFiber20StateAt 13 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix13 ++ [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 13) ttFiber20State13_in_pass1_prefix13

theorem ttFiber20State14_in_pass1_prefix14 :
    ttFiber20StateAt 14 ∈ chainClosureStep ttWord ttFiber20Prefix14 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 6 ∈
      chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix13 = ttFiber20Prefix6 ++ [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13]
      (chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 6) ttFiber20State6_in_pass1_prefix6
  rw [show ttFiber20Prefix14 = ttFiber20Prefix13 ++ [ttFiber20StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 14) []
    (chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 6) hparentBefore ttFiber20ReverseSingleStep14

theorem ttFiber20State14_in_pass1_full :
    ttFiber20StateAt 14 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix14 ++ [ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix14 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 14) ttFiber20State14_in_pass1_prefix14

theorem ttFiber20State15_in_pass1_prefix15 :
    ttFiber20StateAt 15 ∈ chainClosureStep ttWord ttFiber20Prefix15 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 7 ∈
      chainClosureStep ttWord ttFiber20Prefix14 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix14 = ttFiber20Prefix7 ++ [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14]
      (chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 7) ttFiber20State7_in_pass1_prefix7
  rw [show ttFiber20Prefix15 = ttFiber20Prefix14 ++ [ttFiber20StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 15) []
    (chainClosureStep ttWord ttFiber20Prefix14 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 7) hparentBefore ttFiber20ReverseSingleStep15

theorem ttFiber20State15_in_pass1_full :
    ttFiber20StateAt 15 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix15 ++ [ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix15 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 15) ttFiber20State15_in_pass1_prefix15

theorem ttFiber20State18_in_pass1_prefix18 :
    ttFiber20StateAt 18 ∈ chainClosureStep ttWord ttFiber20Prefix18 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 12 ∈
      chainClosureStep ttWord ttFiber20Prefix17 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix17 = ttFiber20Prefix12 ++ [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17]
      (chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 12) ttFiber20State12_in_pass1_prefix12
  rw [show ttFiber20Prefix18 = ttFiber20Prefix17 ++ [ttFiber20StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 18) []
    (chainClosureStep ttWord ttFiber20Prefix17 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 12) hparentBefore ttFiber20ReverseSingleStep18

theorem ttFiber20State18_in_pass1_full :
    ttFiber20StateAt 18 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix18 ++ [ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix18 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 18) ttFiber20State18_in_pass1_prefix18

theorem ttFiber20State19_in_pass1_prefix19 :
    ttFiber20StateAt 19 ∈ chainClosureStep ttWord ttFiber20Prefix19 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 13 ∈
      chainClosureStep ttWord ttFiber20Prefix18 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix18 = ttFiber20Prefix13 ++ [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18]
      (chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 13) ttFiber20State13_in_pass1_prefix13
  rw [show ttFiber20Prefix19 = ttFiber20Prefix18 ++ [ttFiber20StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 19) []
    (chainClosureStep ttWord ttFiber20Prefix18 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 13) hparentBefore ttFiber20ReverseSingleStep19

theorem ttFiber20State19_in_pass1_full :
    ttFiber20StateAt 19 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix19 ++ [ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix19 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 19) ttFiber20State19_in_pass1_prefix19

theorem ttFiber20State20_in_pass1_prefix20 :
    ttFiber20StateAt 20 ∈ chainClosureStep ttWord ttFiber20Prefix20 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 8 ∈
      chainClosureStep ttWord ttFiber20Prefix19 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix19 = ttFiber20Prefix8 ++ [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19]
      (chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 8) ttFiber20State8_in_pass1_prefix8
  rw [show ttFiber20Prefix20 = ttFiber20Prefix19 ++ [ttFiber20StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 20) []
    (chainClosureStep ttWord ttFiber20Prefix19 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 8) hparentBefore ttFiber20ReverseSingleStep20

theorem ttFiber20State20_in_pass1_full :
    ttFiber20StateAt 20 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix20 ++ [ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix20 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 20) ttFiber20State20_in_pass1_prefix20

theorem ttFiber20State21_in_pass1_prefix21 :
    ttFiber20StateAt 21 ∈ chainClosureStep ttWord ttFiber20Prefix21 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 9 ∈
      chainClosureStep ttWord ttFiber20Prefix20 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix20 = ttFiber20Prefix9 ++ [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20]
      (chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 9) ttFiber20State9_in_pass1_prefix9
  rw [show ttFiber20Prefix21 = ttFiber20Prefix20 ++ [ttFiber20StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 21) []
    (chainClosureStep ttWord ttFiber20Prefix20 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 9) hparentBefore ttFiber20ReverseSingleStep21

theorem ttFiber20State21_in_pass1_full :
    ttFiber20StateAt 21 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix21 ++ [ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix21 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 21) ttFiber20State21_in_pass1_prefix21

theorem ttFiber20State22_in_pass1_prefix22 :
    ttFiber20StateAt 22 ∈ chainClosureStep ttWord ttFiber20Prefix22 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 10 ∈
      chainClosureStep ttWord ttFiber20Prefix21 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix21 = ttFiber20Prefix10 ++ [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21]
      (chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 10) ttFiber20State10_in_pass1_prefix10
  rw [show ttFiber20Prefix22 = ttFiber20Prefix21 ++ [ttFiber20StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 22) []
    (chainClosureStep ttWord ttFiber20Prefix21 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 10) hparentBefore ttFiber20ReverseSingleStep22

theorem ttFiber20State22_in_pass1_full :
    ttFiber20StateAt 22 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix22 ++ [ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix22 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 22) ttFiber20State22_in_pass1_prefix22

theorem ttFiber20State23_in_pass1_prefix23 :
    ttFiber20StateAt 23 ∈ chainClosureStep ttWord ttFiber20Prefix23 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 11 ∈
      chainClosureStep ttWord ttFiber20Prefix22 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix22 = ttFiber20Prefix11 ++ [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22]
      (chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 11) ttFiber20State11_in_pass1_prefix11
  rw [show ttFiber20Prefix23 = ttFiber20Prefix22 ++ [ttFiber20StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 23) []
    (chainClosureStep ttWord ttFiber20Prefix22 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 11) hparentBefore ttFiber20ReverseSingleStep23

theorem ttFiber20State23_in_pass1_full :
    ttFiber20StateAt 23 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix23 ++ [ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix23 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 23) ttFiber20State23_in_pass1_prefix23

theorem ttFiber20State26_in_pass1_prefix26 :
    ttFiber20StateAt 26 ∈ chainClosureStep ttWord ttFiber20Prefix26 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 4 ∈
      chainClosureStep ttWord ttFiber20Prefix25 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix25 = ttFiber20Prefix4 ++ [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25]
      (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 4) ttFiber20State4_in_pass1_prefix4
  rw [show ttFiber20Prefix26 = ttFiber20Prefix25 ++ [ttFiber20StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 26) []
    (chainClosureStep ttWord ttFiber20Prefix25 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 4) hparentBefore ttFiber20ReverseSingleStep26

theorem ttFiber20State26_in_pass1_full :
    ttFiber20StateAt 26 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix26 ++ [ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix26 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 26) ttFiber20State26_in_pass1_prefix26

theorem ttFiber20State27_in_pass1_prefix27 :
    ttFiber20StateAt 27 ∈ chainClosureStep ttWord ttFiber20Prefix27 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 5 ∈
      chainClosureStep ttWord ttFiber20Prefix26 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix26 = ttFiber20Prefix5 ++ [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26]
      (chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 5) ttFiber20State5_in_pass1_prefix5
  rw [show ttFiber20Prefix27 = ttFiber20Prefix26 ++ [ttFiber20StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 27) []
    (chainClosureStep ttWord ttFiber20Prefix26 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 5) hparentBefore ttFiber20ReverseSingleStep27

theorem ttFiber20State27_in_pass1_full :
    ttFiber20StateAt 27 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix27 ++ [ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix27 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 27) ttFiber20State27_in_pass1_prefix27

theorem ttFiber20State28_in_pass1_prefix28 :
    ttFiber20StateAt 28 ∈ chainClosureStep ttWord ttFiber20Prefix28 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix27 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix27
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix28 = ttFiber20Prefix27 ++ [ttFiber20StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 28) []
    (chainClosureStep ttWord ttFiber20Prefix27 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep28

theorem ttFiber20State28_in_pass1_full :
    ttFiber20StateAt 28 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix28 ++ [ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix28 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 28) ttFiber20State28_in_pass1_prefix28

theorem ttFiber20State29_in_pass1_prefix29 :
    ttFiber20StateAt 29 ∈ chainClosureStep ttWord ttFiber20Prefix29 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20Prefix28 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix28 = ttFiber20Prefix1 ++ [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28]
      (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1
  rw [show ttFiber20Prefix29 = ttFiber20Prefix28 ++ [ttFiber20StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 29) []
    (chainClosureStep ttWord ttFiber20Prefix28 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) hparentBefore ttFiber20ReverseSingleStep29

theorem ttFiber20State29_in_pass1_full :
    ttFiber20StateAt 29 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix29 ++ [ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix29 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 29) ttFiber20State29_in_pass1_prefix29

theorem ttFiber20State30_in_pass1_prefix30 :
    ttFiber20StateAt 30 ∈ chainClosureStep ttWord ttFiber20Prefix30 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 2 ∈
      chainClosureStep ttWord ttFiber20Prefix29 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix29 = ttFiber20Prefix2 ++ [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29]
      (chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 2) ttFiber20State2_in_pass1_prefix2
  rw [show ttFiber20Prefix30 = ttFiber20Prefix29 ++ [ttFiber20StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 30) []
    (chainClosureStep ttWord ttFiber20Prefix29 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 2) hparentBefore ttFiber20ReverseSingleStep30

theorem ttFiber20State30_in_pass1_full :
    ttFiber20StateAt 30 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix30 ++ [ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix30 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 30) ttFiber20State30_in_pass1_prefix30

theorem ttFiber20State31_in_pass1_prefix31 :
    ttFiber20StateAt 31 ∈ chainClosureStep ttWord ttFiber20Prefix31 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 3 ∈
      chainClosureStep ttWord ttFiber20Prefix30 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix30 = ttFiber20Prefix3 ++ [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30]
      (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 3) ttFiber20State3_in_pass1_prefix3
  rw [show ttFiber20Prefix31 = ttFiber20Prefix30 ++ [ttFiber20StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 31) []
    (chainClosureStep ttWord ttFiber20Prefix30 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 3) hparentBefore ttFiber20ReverseSingleStep31

theorem ttFiber20State31_in_pass1_full :
    ttFiber20StateAt 31 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix31 ++ [ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix31 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 31) ttFiber20State31_in_pass1_prefix31

theorem ttFiber20State32_in_pass1_prefix32 :
    ttFiber20StateAt 32 ∈ chainClosureStep ttWord ttFiber20Prefix32 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 0 ∈
      chainClosureStep ttWord ttFiber20Prefix31 ([ttFiber20StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix31
      ([ttFiber20StateAt 0]) (ttFiber20StateAt 0) ttFiber20State0_in_pass0_full
  rw [show ttFiber20Prefix32 = ttFiber20Prefix31 ++ [ttFiber20StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 32) []
    (chainClosureStep ttWord ttFiber20Prefix31 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 0) hparentBefore ttFiber20ReverseSingleStep32

theorem ttFiber20State32_in_pass1_full :
    ttFiber20StateAt 32 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix32 ++ [ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix32 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 32) ttFiber20State32_in_pass1_prefix32

theorem ttFiber20State33_in_pass1_prefix33 :
    ttFiber20StateAt 33 ∈ chainClosureStep ttWord ttFiber20Prefix33 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 1 ∈
      chainClosureStep ttWord ttFiber20Prefix32 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix32 = ttFiber20Prefix1 ++ [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 2, ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32]
      (chainClosureStep ttWord ttFiber20Prefix1 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 1) ttFiber20State1_in_pass1_prefix1
  rw [show ttFiber20Prefix33 = ttFiber20Prefix32 ++ [ttFiber20StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 33) []
    (chainClosureStep ttWord ttFiber20Prefix32 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 1) hparentBefore ttFiber20ReverseSingleStep33

theorem ttFiber20State33_in_pass1_full :
    ttFiber20StateAt 33 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix33 ++ [ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix33 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 33) ttFiber20State33_in_pass1_prefix33

theorem ttFiber20State34_in_pass1_prefix34 :
    ttFiber20StateAt 34 ∈ chainClosureStep ttWord ttFiber20Prefix34 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 2 ∈
      chainClosureStep ttWord ttFiber20Prefix33 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix33 = ttFiber20Prefix2 ++ [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 3, ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33]
      (chainClosureStep ttWord ttFiber20Prefix2 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 2) ttFiber20State2_in_pass1_prefix2
  rw [show ttFiber20Prefix34 = ttFiber20Prefix33 ++ [ttFiber20StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 34) []
    (chainClosureStep ttWord ttFiber20Prefix33 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 2) hparentBefore ttFiber20ReverseSingleStep34

theorem ttFiber20State34_in_pass1_full :
    ttFiber20StateAt 34 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix34 ++ [ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix34 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 34) ttFiber20State34_in_pass1_prefix34

theorem ttFiber20State35_in_pass1_prefix35 :
    ttFiber20StateAt 35 ∈ chainClosureStep ttWord ttFiber20Prefix35 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 3 ∈
      chainClosureStep ttWord ttFiber20Prefix34 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix34 = ttFiber20Prefix3 ++ [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 4, ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34]
      (chainClosureStep ttWord ttFiber20Prefix3 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 3) ttFiber20State3_in_pass1_prefix3
  rw [show ttFiber20Prefix35 = ttFiber20Prefix34 ++ [ttFiber20StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 35) []
    (chainClosureStep ttWord ttFiber20Prefix34 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 3) hparentBefore ttFiber20ReverseSingleStep35

theorem ttFiber20State35_in_pass1_full :
    ttFiber20StateAt 35 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix35 ++ [ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix35 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 35) ttFiber20State35_in_pass1_prefix35

theorem ttFiber20State36_in_pass1_prefix36 :
    ttFiber20StateAt 36 ∈ chainClosureStep ttWord ttFiber20Prefix36 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 4 ∈
      chainClosureStep ttWord ttFiber20Prefix35 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix35 = ttFiber20Prefix4 ++ [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 5, ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35]
      (chainClosureStep ttWord ttFiber20Prefix4 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 4) ttFiber20State4_in_pass1_prefix4
  rw [show ttFiber20Prefix36 = ttFiber20Prefix35 ++ [ttFiber20StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 36) []
    (chainClosureStep ttWord ttFiber20Prefix35 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 4) hparentBefore ttFiber20ReverseSingleStep36

theorem ttFiber20State36_in_pass1_full :
    ttFiber20StateAt 36 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix36 ++ [ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix36 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 36) ttFiber20State36_in_pass1_prefix36

theorem ttFiber20State37_in_pass1_prefix37 :
    ttFiber20StateAt 37 ∈ chainClosureStep ttWord ttFiber20Prefix37 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 5 ∈
      chainClosureStep ttWord ttFiber20Prefix36 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix36 = ttFiber20Prefix5 ++ [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 6, ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36]
      (chainClosureStep ttWord ttFiber20Prefix5 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 5) ttFiber20State5_in_pass1_prefix5
  rw [show ttFiber20Prefix37 = ttFiber20Prefix36 ++ [ttFiber20StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 37) []
    (chainClosureStep ttWord ttFiber20Prefix36 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 5) hparentBefore ttFiber20ReverseSingleStep37

theorem ttFiber20State37_in_pass1_full :
    ttFiber20StateAt 37 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix37 ++ [ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix37 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 37) ttFiber20State37_in_pass1_prefix37

theorem ttFiber20State38_in_pass1_prefix38 :
    ttFiber20StateAt 38 ∈ chainClosureStep ttWord ttFiber20Prefix38 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 6 ∈
      chainClosureStep ttWord ttFiber20Prefix37 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix37 = ttFiber20Prefix6 ++ [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 7, ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37]
      (chainClosureStep ttWord ttFiber20Prefix6 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 6) ttFiber20State6_in_pass1_prefix6
  rw [show ttFiber20Prefix38 = ttFiber20Prefix37 ++ [ttFiber20StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 38) []
    (chainClosureStep ttWord ttFiber20Prefix37 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 6) hparentBefore ttFiber20ReverseSingleStep38

theorem ttFiber20State38_in_pass1_full :
    ttFiber20StateAt 38 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix38 ++ [ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix38 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 38) ttFiber20State38_in_pass1_prefix38

theorem ttFiber20State39_in_pass1_prefix39 :
    ttFiber20StateAt 39 ∈ chainClosureStep ttWord ttFiber20Prefix39 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 7 ∈
      chainClosureStep ttWord ttFiber20Prefix38 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix38 = ttFiber20Prefix7 ++ [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 8, ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38]
      (chainClosureStep ttWord ttFiber20Prefix7 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 7) ttFiber20State7_in_pass1_prefix7
  rw [show ttFiber20Prefix39 = ttFiber20Prefix38 ++ [ttFiber20StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 39) []
    (chainClosureStep ttWord ttFiber20Prefix38 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 7) hparentBefore ttFiber20ReverseSingleStep39

theorem ttFiber20State39_in_pass1_full :
    ttFiber20StateAt 39 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix39 ++ [ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix39 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 39) ttFiber20State39_in_pass1_prefix39

theorem ttFiber20State40_in_pass1_prefix40 :
    ttFiber20StateAt 40 ∈ chainClosureStep ttWord ttFiber20Prefix40 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 8 ∈
      chainClosureStep ttWord ttFiber20Prefix39 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix39 = ttFiber20Prefix8 ++ [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 9, ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39]
      (chainClosureStep ttWord ttFiber20Prefix8 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 8) ttFiber20State8_in_pass1_prefix8
  rw [show ttFiber20Prefix40 = ttFiber20Prefix39 ++ [ttFiber20StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 40) []
    (chainClosureStep ttWord ttFiber20Prefix39 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 8) hparentBefore ttFiber20ReverseSingleStep40

theorem ttFiber20State40_in_pass1_full :
    ttFiber20StateAt 40 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix40 ++ [ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix40 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 40) ttFiber20State40_in_pass1_prefix40

theorem ttFiber20State41_in_pass1_prefix41 :
    ttFiber20StateAt 41 ∈ chainClosureStep ttWord ttFiber20Prefix41 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 9 ∈
      chainClosureStep ttWord ttFiber20Prefix40 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix40 = ttFiber20Prefix9 ++ [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 10, ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40]
      (chainClosureStep ttWord ttFiber20Prefix9 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 9) ttFiber20State9_in_pass1_prefix9
  rw [show ttFiber20Prefix41 = ttFiber20Prefix40 ++ [ttFiber20StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 41) []
    (chainClosureStep ttWord ttFiber20Prefix40 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 9) hparentBefore ttFiber20ReverseSingleStep41

theorem ttFiber20State41_in_pass1_full :
    ttFiber20StateAt 41 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix41 ++ [ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix41 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 41) ttFiber20State41_in_pass1_prefix41

theorem ttFiber20State42_in_pass1_prefix42 :
    ttFiber20StateAt 42 ∈ chainClosureStep ttWord ttFiber20Prefix42 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 10 ∈
      chainClosureStep ttWord ttFiber20Prefix41 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix41 = ttFiber20Prefix10 ++ [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 11, ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41]
      (chainClosureStep ttWord ttFiber20Prefix10 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 10) ttFiber20State10_in_pass1_prefix10
  rw [show ttFiber20Prefix42 = ttFiber20Prefix41 ++ [ttFiber20StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 42) []
    (chainClosureStep ttWord ttFiber20Prefix41 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 10) hparentBefore ttFiber20ReverseSingleStep42

theorem ttFiber20State42_in_pass1_full :
    ttFiber20StateAt 42 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix42 ++ [ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix42 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 42) ttFiber20State42_in_pass1_prefix42

theorem ttFiber20State43_in_pass1_prefix43 :
    ttFiber20StateAt 43 ∈ chainClosureStep ttWord ttFiber20Prefix43 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 11 ∈
      chainClosureStep ttWord ttFiber20Prefix42 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix42 = ttFiber20Prefix11 ++ [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 12, ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42]
      (chainClosureStep ttWord ttFiber20Prefix11 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 11) ttFiber20State11_in_pass1_prefix11
  rw [show ttFiber20Prefix43 = ttFiber20Prefix42 ++ [ttFiber20StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 43) []
    (chainClosureStep ttWord ttFiber20Prefix42 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 11) hparentBefore ttFiber20ReverseSingleStep43

theorem ttFiber20State43_in_pass1_full :
    ttFiber20StateAt 43 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix43 ++ [ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix43 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 43) ttFiber20State43_in_pass1_prefix43

theorem ttFiber20State44_in_pass1_prefix44 :
    ttFiber20StateAt 44 ∈ chainClosureStep ttWord ttFiber20Prefix44 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 12 ∈
      chainClosureStep ttWord ttFiber20Prefix43 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix43 = ttFiber20Prefix12 ++ [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 13, ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43]
      (chainClosureStep ttWord ttFiber20Prefix12 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 12) ttFiber20State12_in_pass1_prefix12
  rw [show ttFiber20Prefix44 = ttFiber20Prefix43 ++ [ttFiber20StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 44) []
    (chainClosureStep ttWord ttFiber20Prefix43 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 12) hparentBefore ttFiber20ReverseSingleStep44

theorem ttFiber20State44_in_pass1_full :
    ttFiber20StateAt 44 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix44 ++ [ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix44 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 44) ttFiber20State44_in_pass1_prefix44

theorem ttFiber20State45_in_pass1_prefix45 :
    ttFiber20StateAt 45 ∈ chainClosureStep ttWord ttFiber20Prefix45 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 13 ∈
      chainClosureStep ttWord ttFiber20Prefix44 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix44 = ttFiber20Prefix13 ++ [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 14, ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44]
      (chainClosureStep ttWord ttFiber20Prefix13 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 13) ttFiber20State13_in_pass1_prefix13
  rw [show ttFiber20Prefix45 = ttFiber20Prefix44 ++ [ttFiber20StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 45) []
    (chainClosureStep ttWord ttFiber20Prefix44 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 13) hparentBefore ttFiber20ReverseSingleStep45

theorem ttFiber20State45_in_pass1_full :
    ttFiber20StateAt 45 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix45 ++ [ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix45 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 45) ttFiber20State45_in_pass1_prefix45

theorem ttFiber20State46_in_pass1_prefix46 :
    ttFiber20StateAt 46 ∈ chainClosureStep ttWord ttFiber20Prefix46 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 14 ∈
      chainClosureStep ttWord ttFiber20Prefix45 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix45 = ttFiber20Prefix14 ++ [ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 15, ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45]
      (chainClosureStep ttWord ttFiber20Prefix14 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 14) ttFiber20State14_in_pass1_prefix14
  rw [show ttFiber20Prefix46 = ttFiber20Prefix45 ++ [ttFiber20StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 46) []
    (chainClosureStep ttWord ttFiber20Prefix45 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 14) hparentBefore ttFiber20ReverseSingleStep46

theorem ttFiber20State46_in_pass1_full :
    ttFiber20StateAt 46 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix46 ++ [ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix46 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 46) ttFiber20State46_in_pass1_prefix46

theorem ttFiber20State47_in_pass1_prefix47 :
    ttFiber20StateAt 47 ∈ chainClosureStep ttWord ttFiber20Prefix47 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 15 ∈
      chainClosureStep ttWord ttFiber20Prefix46 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix46 = ttFiber20Prefix15 ++ [ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 16, ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46]
      (chainClosureStep ttWord ttFiber20Prefix15 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 15) ttFiber20State15_in_pass1_prefix15
  rw [show ttFiber20Prefix47 = ttFiber20Prefix46 ++ [ttFiber20StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 47) []
    (chainClosureStep ttWord ttFiber20Prefix46 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 15) hparentBefore ttFiber20ReverseSingleStep47

theorem ttFiber20State47_in_pass1_full :
    ttFiber20StateAt 47 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix47 ++ [ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix47 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 47) ttFiber20State47_in_pass1_prefix47

theorem ttFiber20State48_in_pass1_prefix48 :
    ttFiber20StateAt 48 ∈ chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 32 ∈
      chainClosureStep ttWord ttFiber20Prefix47 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix47 = ttFiber20Prefix32 ++ [ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47]
      (chainClosureStep ttWord ttFiber20Prefix32 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 32) ttFiber20State32_in_pass1_prefix32
  rw [show ttFiber20Prefix48 = ttFiber20Prefix47 ++ [ttFiber20StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 48) []
    (chainClosureStep ttWord ttFiber20Prefix47 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 32) hparentBefore ttFiber20ReverseSingleStep48

theorem ttFiber20State48_in_pass1_full :
    ttFiber20StateAt 48 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix48 ++ [ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 48) ttFiber20State48_in_pass1_prefix48

theorem ttFiber20State49_in_pass1_prefix49 :
    ttFiber20StateAt 49 ∈ chainClosureStep ttWord ttFiber20Prefix49 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 33 ∈
      chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix48 = ttFiber20Prefix33 ++ [ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48]
      (chainClosureStep ttWord ttFiber20Prefix33 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 33) ttFiber20State33_in_pass1_prefix33
  rw [show ttFiber20Prefix49 = ttFiber20Prefix48 ++ [ttFiber20StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 49) []
    (chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 33) hparentBefore ttFiber20ReverseSingleStep49

theorem ttFiber20State49_in_pass1_full :
    ttFiber20StateAt 49 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix49 ++ [ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix49 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 49) ttFiber20State49_in_pass1_prefix49

theorem ttFiber20State50_in_pass1_prefix50 :
    ttFiber20StateAt 50 ∈ chainClosureStep ttWord ttFiber20Prefix50 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 48 ∈
      chainClosureStep ttWord ttFiber20Prefix49 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix49 = ttFiber20Prefix48 ++ [ttFiber20StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 49]
      (chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 48) ttFiber20State48_in_pass1_prefix48
  rw [show ttFiber20Prefix50 = ttFiber20Prefix49 ++ [ttFiber20StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 50) []
    (chainClosureStep ttWord ttFiber20Prefix49 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 48) hparentBefore ttFiber20ReverseSingleStep50

theorem ttFiber20State50_in_pass1_full :
    ttFiber20StateAt 50 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix50 ++ [ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix50 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 50) ttFiber20State50_in_pass1_prefix50

theorem ttFiber20State51_in_pass1_prefix51 :
    ttFiber20StateAt 51 ∈ chainClosureStep ttWord ttFiber20Prefix51 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 35 ∈
      chainClosureStep ttWord ttFiber20Prefix50 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix50 = ttFiber20Prefix35 ++ [ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50]
      (chainClosureStep ttWord ttFiber20Prefix35 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 35) ttFiber20State35_in_pass1_prefix35
  rw [show ttFiber20Prefix51 = ttFiber20Prefix50 ++ [ttFiber20StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 51) []
    (chainClosureStep ttWord ttFiber20Prefix50 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 35) hparentBefore ttFiber20ReverseSingleStep51

theorem ttFiber20State51_in_pass1_full :
    ttFiber20StateAt 51 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix51 ++ [ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix51 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 51) ttFiber20State51_in_pass1_prefix51

theorem ttFiber20State52_in_pass1_prefix52 :
    ttFiber20StateAt 52 ∈ chainClosureStep ttWord ttFiber20Prefix52 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 36 ∈
      chainClosureStep ttWord ttFiber20Prefix51 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix51 = ttFiber20Prefix36 ++ [ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51]
      (chainClosureStep ttWord ttFiber20Prefix36 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 36) ttFiber20State36_in_pass1_prefix36
  rw [show ttFiber20Prefix52 = ttFiber20Prefix51 ++ [ttFiber20StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 52) []
    (chainClosureStep ttWord ttFiber20Prefix51 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 36) hparentBefore ttFiber20ReverseSingleStep52

theorem ttFiber20State52_in_pass1_full :
    ttFiber20StateAt 52 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix52 ++ [ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix52 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 52) ttFiber20State52_in_pass1_prefix52

theorem ttFiber20State53_in_pass1_prefix53 :
    ttFiber20StateAt 53 ∈ chainClosureStep ttWord ttFiber20Prefix53 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 37 ∈
      chainClosureStep ttWord ttFiber20Prefix52 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix52 = ttFiber20Prefix37 ++ [ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52]
      (chainClosureStep ttWord ttFiber20Prefix37 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 37) ttFiber20State37_in_pass1_prefix37
  rw [show ttFiber20Prefix53 = ttFiber20Prefix52 ++ [ttFiber20StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 53) []
    (chainClosureStep ttWord ttFiber20Prefix52 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 37) hparentBefore ttFiber20ReverseSingleStep53

theorem ttFiber20State53_in_pass1_full :
    ttFiber20StateAt 53 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix53 ++ [ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix53 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 53) ttFiber20State53_in_pass1_prefix53

theorem ttFiber20State54_in_pass1_prefix54 :
    ttFiber20StateAt 54 ∈ chainClosureStep ttWord ttFiber20Prefix54 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 49 ∈
      chainClosureStep ttWord ttFiber20Prefix53 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix53 = ttFiber20Prefix49 ++ [ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53]
      (chainClosureStep ttWord ttFiber20Prefix49 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 49) ttFiber20State49_in_pass1_prefix49
  rw [show ttFiber20Prefix54 = ttFiber20Prefix53 ++ [ttFiber20StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 54) []
    (chainClosureStep ttWord ttFiber20Prefix53 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 49) hparentBefore ttFiber20ReverseSingleStep54

theorem ttFiber20State54_in_pass1_full :
    ttFiber20StateAt 54 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix54 ++ [ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix54 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 54) ttFiber20State54_in_pass1_prefix54

theorem ttFiber20State55_in_pass1_prefix55 :
    ttFiber20StateAt 55 ∈ chainClosureStep ttWord ttFiber20Prefix55 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 48 ∈
      chainClosureStep ttWord ttFiber20Prefix54 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix54 = ttFiber20Prefix48 ++ [ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54]
      (chainClosureStep ttWord ttFiber20Prefix48 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 48) ttFiber20State48_in_pass1_prefix48
  rw [show ttFiber20Prefix55 = ttFiber20Prefix54 ++ [ttFiber20StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 55) []
    (chainClosureStep ttWord ttFiber20Prefix54 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 48) hparentBefore ttFiber20ReverseSingleStep55

theorem ttFiber20State55_in_pass1_full :
    ttFiber20StateAt 55 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix55 ++ [ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix55 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 55) ttFiber20State55_in_pass1_prefix55

theorem ttFiber20State56_in_pass1_prefix56 :
    ttFiber20StateAt 56 ∈ chainClosureStep ttWord ttFiber20Prefix56 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 40 ∈
      chainClosureStep ttWord ttFiber20Prefix55 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix55 = ttFiber20Prefix40 ++ [ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55]
      (chainClosureStep ttWord ttFiber20Prefix40 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 40) ttFiber20State40_in_pass1_prefix40
  rw [show ttFiber20Prefix56 = ttFiber20Prefix55 ++ [ttFiber20StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 56) []
    (chainClosureStep ttWord ttFiber20Prefix55 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 40) hparentBefore ttFiber20ReverseSingleStep56

theorem ttFiber20State56_in_pass1_full :
    ttFiber20StateAt 56 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix56 ++ [ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix56 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 56) ttFiber20State56_in_pass1_prefix56

theorem ttFiber20State57_in_pass1_prefix57 :
    ttFiber20StateAt 57 ∈ chainClosureStep ttWord ttFiber20Prefix57 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 41 ∈
      chainClosureStep ttWord ttFiber20Prefix56 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix56 = ttFiber20Prefix41 ++ [ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56]
      (chainClosureStep ttWord ttFiber20Prefix41 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 41) ttFiber20State41_in_pass1_prefix41
  rw [show ttFiber20Prefix57 = ttFiber20Prefix56 ++ [ttFiber20StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 57) []
    (chainClosureStep ttWord ttFiber20Prefix56 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 41) hparentBefore ttFiber20ReverseSingleStep57

theorem ttFiber20State57_in_pass1_full :
    ttFiber20StateAt 57 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix57 ++ [ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix57 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 57) ttFiber20State57_in_pass1_prefix57

theorem ttFiber20State58_in_pass1_prefix58 :
    ttFiber20StateAt 58 ∈ chainClosureStep ttWord ttFiber20Prefix58 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 26 ∈
      chainClosureStep ttWord ttFiber20Prefix57 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix57 = ttFiber20Prefix26 ++ [ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57]
      (chainClosureStep ttWord ttFiber20Prefix26 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 26) ttFiber20State26_in_pass1_prefix26
  rw [show ttFiber20Prefix58 = ttFiber20Prefix57 ++ [ttFiber20StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 58) []
    (chainClosureStep ttWord ttFiber20Prefix57 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 26) hparentBefore ttFiber20ReverseSingleStep58

theorem ttFiber20State58_in_pass1_full :
    ttFiber20StateAt 58 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix58 ++ [ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix58 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 58) ttFiber20State58_in_pass1_prefix58

theorem ttFiber20State59_in_pass1_prefix59 :
    ttFiber20StateAt 59 ∈ chainClosureStep ttWord ttFiber20Prefix59 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 27 ∈
      chainClosureStep ttWord ttFiber20Prefix58 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix58 = ttFiber20Prefix27 ++ [ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58]
      (chainClosureStep ttWord ttFiber20Prefix27 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 27) ttFiber20State27_in_pass1_prefix27
  rw [show ttFiber20Prefix59 = ttFiber20Prefix58 ++ [ttFiber20StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 59) []
    (chainClosureStep ttWord ttFiber20Prefix58 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 27) hparentBefore ttFiber20ReverseSingleStep59

theorem ttFiber20State59_in_pass1_full :
    ttFiber20StateAt 59 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix59 ++ [ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix59 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 59) ttFiber20State59_in_pass1_prefix59

theorem ttFiber20State60_in_pass1_prefix60 :
    ttFiber20StateAt 60 ∈ chainClosureStep ttWord ttFiber20Prefix60 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 28 ∈
      chainClosureStep ttWord ttFiber20Prefix59 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix59 = ttFiber20Prefix28 ++ [ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59]
      (chainClosureStep ttWord ttFiber20Prefix28 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 28) ttFiber20State28_in_pass1_prefix28
  rw [show ttFiber20Prefix60 = ttFiber20Prefix59 ++ [ttFiber20StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 60) []
    (chainClosureStep ttWord ttFiber20Prefix59 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 28) hparentBefore ttFiber20ReverseSingleStep60

theorem ttFiber20State60_in_pass1_full :
    ttFiber20StateAt 60 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix60 ++ [ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix60 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 60) ttFiber20State60_in_pass1_prefix60

theorem ttFiber20State61_in_pass1_prefix61 :
    ttFiber20StateAt 61 ∈ chainClosureStep ttWord ttFiber20Prefix61 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 29 ∈
      chainClosureStep ttWord ttFiber20Prefix60 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix60 = ttFiber20Prefix29 ++ [ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60]
      (chainClosureStep ttWord ttFiber20Prefix29 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 29) ttFiber20State29_in_pass1_prefix29
  rw [show ttFiber20Prefix61 = ttFiber20Prefix60 ++ [ttFiber20StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 61) []
    (chainClosureStep ttWord ttFiber20Prefix60 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 29) hparentBefore ttFiber20ReverseSingleStep61

theorem ttFiber20State61_in_pass1_full :
    ttFiber20StateAt 61 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix61 ++ [ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix61 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 61) ttFiber20State61_in_pass1_prefix61

theorem ttFiber20State62_in_pass1_prefix62 :
    ttFiber20StateAt 62 ∈ chainClosureStep ttWord ttFiber20Prefix62 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 60 ∈
      chainClosureStep ttWord ttFiber20Prefix61 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix61 = ttFiber20Prefix60 ++ [ttFiber20StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 61]
      (chainClosureStep ttWord ttFiber20Prefix60 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 60) ttFiber20State60_in_pass1_prefix60
  rw [show ttFiber20Prefix62 = ttFiber20Prefix61 ++ [ttFiber20StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 62) []
    (chainClosureStep ttWord ttFiber20Prefix61 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 60) hparentBefore ttFiber20ReverseSingleStep62

theorem ttFiber20State62_in_pass1_full :
    ttFiber20StateAt 62 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix62 ++ [ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix62 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 62) ttFiber20State62_in_pass1_prefix62

theorem ttFiber20State63_in_pass1_prefix63 :
    ttFiber20StateAt 63 ∈ chainClosureStep ttWord ttFiber20Prefix63 ([ttFiber20StateAt 0]) := by
  have hparentBefore : ttFiber20StateAt 31 ∈
      chainClosureStep ttWord ttFiber20Prefix62 ([ttFiber20StateAt 0]) := by
    rw [show ttFiber20Prefix62 = ttFiber20Prefix31 ++ [ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62]
      (chainClosureStep ttWord ttFiber20Prefix31 ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 31) ttFiber20State31_in_pass1_prefix31
  rw [show ttFiber20Prefix63 = ttFiber20Prefix62 ++ [ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 63) []
    (chainClosureStep ttWord ttFiber20Prefix62 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 31) hparentBefore ttFiber20ReverseSingleStep63

theorem ttFiber20State63_in_pass1_full :
    ttFiber20StateAt 63 ∈ chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber20Prefix63 ([ttFiber20StateAt 0]))
    (ttFiber20StateAt 63) ttFiber20State63_in_pass1_prefix63

theorem ttFiber20State16_in_pass2_prefix16 :
    ttFiber20StateAt 16 ∈ chainClosureStep ttWord ttFiber20Prefix16 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  have hparentBefore : ttFiber20StateAt 20 ∈
      chainClosureStep ttWord ttFiber20Prefix15 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix15
      (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 20) ttFiber20State20_in_pass1_full
  rw [show ttFiber20Prefix16 = ttFiber20Prefix15 ++ [ttFiber20StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 16) []
    (chainClosureStep ttWord ttFiber20Prefix15 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 20) hparentBefore ttFiber20ReverseSingleStep16

theorem ttFiber20State16_in_pass2_full :
    ttFiber20StateAt 16 ∈ chainClosureStep ttWord ttFiber20DirectStates (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix16 ++ [ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 17, ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix16 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 16) ttFiber20State16_in_pass2_prefix16

theorem ttFiber20State17_in_pass2_prefix17 :
    ttFiber20StateAt 17 ∈ chainClosureStep ttWord ttFiber20Prefix17 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  have hparentBefore : ttFiber20StateAt 21 ∈
      chainClosureStep ttWord ttFiber20Prefix16 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix16
      (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 21) ttFiber20State21_in_pass1_full
  rw [show ttFiber20Prefix17 = ttFiber20Prefix16 ++ [ttFiber20StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 17) []
    (chainClosureStep ttWord ttFiber20Prefix16 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 21) hparentBefore ttFiber20ReverseSingleStep17

theorem ttFiber20State17_in_pass2_full :
    ttFiber20StateAt 17 ∈ chainClosureStep ttWord ttFiber20DirectStates (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix17 ++ [ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 18, ttFiber20StateAt 19, ttFiber20StateAt 20, ttFiber20StateAt 21, ttFiber20StateAt 22, ttFiber20StateAt 23, ttFiber20StateAt 24, ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix17 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 17) ttFiber20State17_in_pass2_prefix17

theorem ttFiber20State24_in_pass2_prefix24 :
    ttFiber20StateAt 24 ∈ chainClosureStep ttWord ttFiber20Prefix24 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  have hparentBefore : ttFiber20StateAt 28 ∈
      chainClosureStep ttWord ttFiber20Prefix23 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix23
      (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 28) ttFiber20State28_in_pass1_full
  rw [show ttFiber20Prefix24 = ttFiber20Prefix23 ++ [ttFiber20StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 24) []
    (chainClosureStep ttWord ttFiber20Prefix23 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 28) hparentBefore ttFiber20ReverseSingleStep24

theorem ttFiber20State24_in_pass2_full :
    ttFiber20StateAt 24 ∈ chainClosureStep ttWord ttFiber20DirectStates (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix24 ++ [ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 25, ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix24 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 24) ttFiber20State24_in_pass2_prefix24

theorem ttFiber20State25_in_pass2_prefix25 :
    ttFiber20StateAt 25 ∈ chainClosureStep ttWord ttFiber20Prefix25 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  have hparentBefore : ttFiber20StateAt 29 ∈
      chainClosureStep ttWord ttFiber20Prefix24 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber20Prefix24
      (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0]))
      (ttFiber20StateAt 29) ttFiber20State29_in_pass1_full
  rw [show ttFiber20Prefix25 = ttFiber20Prefix24 ++ [ttFiber20StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber20StateAt 25) []
    (chainClosureStep ttWord ttFiber20Prefix24 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 29) hparentBefore ttFiber20ReverseSingleStep25

theorem ttFiber20State25_in_pass2_full :
    ttFiber20StateAt 25 ∈ chainClosureStep ttWord ttFiber20DirectStates (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])) := by
  rw [show ttFiber20DirectStates = ttFiber20Prefix25 ++ [ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber20StateAt 26, ttFiber20StateAt 27, ttFiber20StateAt 28, ttFiber20StateAt 29, ttFiber20StateAt 30, ttFiber20StateAt 31, ttFiber20StateAt 32, ttFiber20StateAt 33, ttFiber20StateAt 34, ttFiber20StateAt 35, ttFiber20StateAt 36, ttFiber20StateAt 37, ttFiber20StateAt 38, ttFiber20StateAt 39, ttFiber20StateAt 40, ttFiber20StateAt 41, ttFiber20StateAt 42, ttFiber20StateAt 43, ttFiber20StateAt 44, ttFiber20StateAt 45, ttFiber20StateAt 46, ttFiber20StateAt 47, ttFiber20StateAt 48, ttFiber20StateAt 49, ttFiber20StateAt 50, ttFiber20StateAt 51, ttFiber20StateAt 52, ttFiber20StateAt 53, ttFiber20StateAt 54, ttFiber20StateAt 55, ttFiber20StateAt 56, ttFiber20StateAt 57, ttFiber20StateAt 58, ttFiber20StateAt 59, ttFiber20StateAt 60, ttFiber20StateAt 61, ttFiber20StateAt 62, ttFiber20StateAt 63]
    (chainClosureStep ttWord ttFiber20Prefix25 (chainClosureStep ttWord ttFiber20DirectStates ([ttFiber20StateAt 0])))
    (ttFiber20StateAt 25) ttFiber20State25_in_pass2_prefix25

theorem ttFiber20State0_in_close :
    ttFiber20StateAt 0 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber20DirectStates ttFiber20DirectStates.length
    [ttFiber20StateAt 0] (ttFiber20StateAt 0) (by simp)

theorem ttFiber20State1_in_close :
    ttFiber20StateAt 1 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 1 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 1) ttFiber20State1_in_pass1_full

theorem ttFiber20State2_in_close :
    ttFiber20StateAt 2 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 2 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 2) ttFiber20State2_in_pass1_full

theorem ttFiber20State3_in_close :
    ttFiber20StateAt 3 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 3 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 3) ttFiber20State3_in_pass1_full

theorem ttFiber20State4_in_close :
    ttFiber20StateAt 4 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 4 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 4) ttFiber20State4_in_pass1_full

theorem ttFiber20State5_in_close :
    ttFiber20StateAt 5 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 5 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 5) ttFiber20State5_in_pass1_full

theorem ttFiber20State6_in_close :
    ttFiber20StateAt 6 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 6 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 6) ttFiber20State6_in_pass1_full

theorem ttFiber20State7_in_close :
    ttFiber20StateAt 7 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 7 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 7) ttFiber20State7_in_pass1_full

theorem ttFiber20State8_in_close :
    ttFiber20StateAt 8 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 8 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 8) ttFiber20State8_in_pass1_full

theorem ttFiber20State9_in_close :
    ttFiber20StateAt 9 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 9 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 9) ttFiber20State9_in_pass1_full

theorem ttFiber20State10_in_close :
    ttFiber20StateAt 10 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 10 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 10) ttFiber20State10_in_pass1_full

theorem ttFiber20State11_in_close :
    ttFiber20StateAt 11 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 11 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 11) ttFiber20State11_in_pass1_full

theorem ttFiber20State12_in_close :
    ttFiber20StateAt 12 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 12 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 12) ttFiber20State12_in_pass1_full

theorem ttFiber20State13_in_close :
    ttFiber20StateAt 13 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 13 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 13) ttFiber20State13_in_pass1_full

theorem ttFiber20State14_in_close :
    ttFiber20StateAt 14 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 14 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 14) ttFiber20State14_in_pass1_full

theorem ttFiber20State15_in_close :
    ttFiber20StateAt 15 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 15 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 15) ttFiber20State15_in_pass1_full

theorem ttFiber20State16_in_close :
    ttFiber20StateAt 16 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 16 ∈ closeChainFiber ttWord ttFiber20DirectStates (62 + 2)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber20DirectStates 62
    [ttFiber20StateAt 0] (ttFiber20StateAt 16) ttFiber20FirstPassGrows
    ttFiber20State16_in_pass2_full

theorem ttFiber20State17_in_close :
    ttFiber20StateAt 17 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 17 ∈ closeChainFiber ttWord ttFiber20DirectStates (62 + 2)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber20DirectStates 62
    [ttFiber20StateAt 0] (ttFiber20StateAt 17) ttFiber20FirstPassGrows
    ttFiber20State17_in_pass2_full

theorem ttFiber20State18_in_close :
    ttFiber20StateAt 18 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 18 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 18) ttFiber20State18_in_pass1_full

theorem ttFiber20State19_in_close :
    ttFiber20StateAt 19 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 19 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 19) ttFiber20State19_in_pass1_full

theorem ttFiber20State20_in_close :
    ttFiber20StateAt 20 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 20 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 20) ttFiber20State20_in_pass1_full

theorem ttFiber20State21_in_close :
    ttFiber20StateAt 21 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 21 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 21) ttFiber20State21_in_pass1_full

theorem ttFiber20State22_in_close :
    ttFiber20StateAt 22 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 22 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 22) ttFiber20State22_in_pass1_full

theorem ttFiber20State23_in_close :
    ttFiber20StateAt 23 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 23 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 23) ttFiber20State23_in_pass1_full

theorem ttFiber20State24_in_close :
    ttFiber20StateAt 24 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 24 ∈ closeChainFiber ttWord ttFiber20DirectStates (62 + 2)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber20DirectStates 62
    [ttFiber20StateAt 0] (ttFiber20StateAt 24) ttFiber20FirstPassGrows
    ttFiber20State24_in_pass2_full

theorem ttFiber20State25_in_close :
    ttFiber20StateAt 25 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 25 ∈ closeChainFiber ttWord ttFiber20DirectStates (62 + 2)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber20DirectStates 62
    [ttFiber20StateAt 0] (ttFiber20StateAt 25) ttFiber20FirstPassGrows
    ttFiber20State25_in_pass2_full

theorem ttFiber20State26_in_close :
    ttFiber20StateAt 26 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 26 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 26) ttFiber20State26_in_pass1_full

theorem ttFiber20State27_in_close :
    ttFiber20StateAt 27 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 27 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 27) ttFiber20State27_in_pass1_full

theorem ttFiber20State28_in_close :
    ttFiber20StateAt 28 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 28 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 28) ttFiber20State28_in_pass1_full

theorem ttFiber20State29_in_close :
    ttFiber20StateAt 29 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 29 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 29) ttFiber20State29_in_pass1_full

theorem ttFiber20State30_in_close :
    ttFiber20StateAt 30 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 30 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 30) ttFiber20State30_in_pass1_full

theorem ttFiber20State31_in_close :
    ttFiber20StateAt 31 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 31 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 31) ttFiber20State31_in_pass1_full

theorem ttFiber20State32_in_close :
    ttFiber20StateAt 32 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 32 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 32) ttFiber20State32_in_pass1_full

theorem ttFiber20State33_in_close :
    ttFiber20StateAt 33 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 33 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 33) ttFiber20State33_in_pass1_full

theorem ttFiber20State34_in_close :
    ttFiber20StateAt 34 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 34 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 34) ttFiber20State34_in_pass1_full

theorem ttFiber20State35_in_close :
    ttFiber20StateAt 35 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 35 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 35) ttFiber20State35_in_pass1_full

theorem ttFiber20State36_in_close :
    ttFiber20StateAt 36 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 36 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 36) ttFiber20State36_in_pass1_full

theorem ttFiber20State37_in_close :
    ttFiber20StateAt 37 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 37 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 37) ttFiber20State37_in_pass1_full

theorem ttFiber20State38_in_close :
    ttFiber20StateAt 38 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 38 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 38) ttFiber20State38_in_pass1_full

theorem ttFiber20State39_in_close :
    ttFiber20StateAt 39 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 39 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 39) ttFiber20State39_in_pass1_full

theorem ttFiber20State40_in_close :
    ttFiber20StateAt 40 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 40 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 40) ttFiber20State40_in_pass1_full

theorem ttFiber20State41_in_close :
    ttFiber20StateAt 41 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 41 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 41) ttFiber20State41_in_pass1_full

theorem ttFiber20State42_in_close :
    ttFiber20StateAt 42 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 42 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 42) ttFiber20State42_in_pass1_full

theorem ttFiber20State43_in_close :
    ttFiber20StateAt 43 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 43 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 43) ttFiber20State43_in_pass1_full

theorem ttFiber20State44_in_close :
    ttFiber20StateAt 44 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 44 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 44) ttFiber20State44_in_pass1_full

theorem ttFiber20State45_in_close :
    ttFiber20StateAt 45 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 45 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 45) ttFiber20State45_in_pass1_full

theorem ttFiber20State46_in_close :
    ttFiber20StateAt 46 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 46 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 46) ttFiber20State46_in_pass1_full

theorem ttFiber20State47_in_close :
    ttFiber20StateAt 47 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 47 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 47) ttFiber20State47_in_pass1_full

theorem ttFiber20State48_in_close :
    ttFiber20StateAt 48 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 48 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 48) ttFiber20State48_in_pass1_full

theorem ttFiber20State49_in_close :
    ttFiber20StateAt 49 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 49 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 49) ttFiber20State49_in_pass1_full

theorem ttFiber20State50_in_close :
    ttFiber20StateAt 50 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 50 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 50) ttFiber20State50_in_pass1_full

theorem ttFiber20State51_in_close :
    ttFiber20StateAt 51 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 51 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 51) ttFiber20State51_in_pass1_full

theorem ttFiber20State52_in_close :
    ttFiber20StateAt 52 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 52 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 52) ttFiber20State52_in_pass1_full

theorem ttFiber20State53_in_close :
    ttFiber20StateAt 53 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 53 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 53) ttFiber20State53_in_pass1_full

theorem ttFiber20State54_in_close :
    ttFiber20StateAt 54 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 54 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 54) ttFiber20State54_in_pass1_full

theorem ttFiber20State55_in_close :
    ttFiber20StateAt 55 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 55 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 55) ttFiber20State55_in_pass1_full

theorem ttFiber20State56_in_close :
    ttFiber20StateAt 56 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 56 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 56) ttFiber20State56_in_pass1_full

theorem ttFiber20State57_in_close :
    ttFiber20StateAt 57 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 57 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 57) ttFiber20State57_in_pass1_full

theorem ttFiber20State58_in_close :
    ttFiber20StateAt 58 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 58 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 58) ttFiber20State58_in_pass1_full

theorem ttFiber20State59_in_close :
    ttFiber20StateAt 59 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 59 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 59) ttFiber20State59_in_pass1_full

theorem ttFiber20State60_in_close :
    ttFiber20StateAt 60 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 60 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 60) ttFiber20State60_in_pass1_full

theorem ttFiber20State61_in_close :
    ttFiber20StateAt 61 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 61 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 61) ttFiber20State61_in_pass1_full

theorem ttFiber20State62_in_close :
    ttFiber20StateAt 62 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 62 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 62) ttFiber20State62_in_pass1_full

theorem ttFiber20State63_in_close :
    ttFiber20StateAt 63 ∈
      closeChainFiber ttWord ttFiber20DirectStates ttFiber20DirectStates.length
        [ttFiber20StateAt 0] := by
  change ttFiber20StateAt 63 ∈ closeChainFiber ttWord ttFiber20DirectStates (63 + 1)
    [ttFiber20StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber20DirectStates 63
    [ttFiber20StateAt 0] (ttFiber20StateAt 63) ttFiber20State63_in_pass1_full

theorem ttFiber20DirectConnected :
    chainFiberConnected ttWord ttFiber20DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber20DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber20State0_in_close
  · subst state
    exact ttFiber20State1_in_close
  · subst state
    exact ttFiber20State2_in_close
  · subst state
    exact ttFiber20State3_in_close
  · subst state
    exact ttFiber20State4_in_close
  · subst state
    exact ttFiber20State5_in_close
  · subst state
    exact ttFiber20State6_in_close
  · subst state
    exact ttFiber20State7_in_close
  · subst state
    exact ttFiber20State8_in_close
  · subst state
    exact ttFiber20State9_in_close
  · subst state
    exact ttFiber20State10_in_close
  · subst state
    exact ttFiber20State11_in_close
  · subst state
    exact ttFiber20State12_in_close
  · subst state
    exact ttFiber20State13_in_close
  · subst state
    exact ttFiber20State14_in_close
  · subst state
    exact ttFiber20State15_in_close
  · subst state
    exact ttFiber20State16_in_close
  · subst state
    exact ttFiber20State17_in_close
  · subst state
    exact ttFiber20State18_in_close
  · subst state
    exact ttFiber20State19_in_close
  · subst state
    exact ttFiber20State20_in_close
  · subst state
    exact ttFiber20State21_in_close
  · subst state
    exact ttFiber20State22_in_close
  · subst state
    exact ttFiber20State23_in_close
  · subst state
    exact ttFiber20State24_in_close
  · subst state
    exact ttFiber20State25_in_close
  · subst state
    exact ttFiber20State26_in_close
  · subst state
    exact ttFiber20State27_in_close
  · subst state
    exact ttFiber20State28_in_close
  · subst state
    exact ttFiber20State29_in_close
  · subst state
    exact ttFiber20State30_in_close
  · subst state
    exact ttFiber20State31_in_close
  · subst state
    exact ttFiber20State32_in_close
  · subst state
    exact ttFiber20State33_in_close
  · subst state
    exact ttFiber20State34_in_close
  · subst state
    exact ttFiber20State35_in_close
  · subst state
    exact ttFiber20State36_in_close
  · subst state
    exact ttFiber20State37_in_close
  · subst state
    exact ttFiber20State38_in_close
  · subst state
    exact ttFiber20State39_in_close
  · subst state
    exact ttFiber20State40_in_close
  · subst state
    exact ttFiber20State41_in_close
  · subst state
    exact ttFiber20State42_in_close
  · subst state
    exact ttFiber20State43_in_close
  · subst state
    exact ttFiber20State44_in_close
  · subst state
    exact ttFiber20State45_in_close
  · subst state
    exact ttFiber20State46_in_close
  · subst state
    exact ttFiber20State47_in_close
  · subst state
    exact ttFiber20State48_in_close
  · subst state
    exact ttFiber20State49_in_close
  · subst state
    exact ttFiber20State50_in_close
  · subst state
    exact ttFiber20State51_in_close
  · subst state
    exact ttFiber20State52_in_close
  · subst state
    exact ttFiber20State53_in_close
  · subst state
    exact ttFiber20State54_in_close
  · subst state
    exact ttFiber20State55_in_close
  · subst state
    exact ttFiber20State56_in_close
  · subst state
    exact ttFiber20State57_in_close
  · subst state
    exact ttFiber20State58_in_close
  · subst state
    exact ttFiber20State59_in_close
  · subst state
    exact ttFiber20State60_in_close
  · subst state
    exact ttFiber20State61_in_close
  · subst state
    exact ttFiber20State62_in_close
  · subst state
    exact ttFiber20State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
