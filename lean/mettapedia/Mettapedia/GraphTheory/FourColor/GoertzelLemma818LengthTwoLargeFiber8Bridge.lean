import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber8

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber8StateAt (i : Nat) : List TauState :=
  directStates (ttFiber8RowAt i).sourceLeft (ttFiber8RowAt i).sourceRight

def ttFiber8DirectStates : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]

def ttFiber8Prefix0 : List (List TauState) :=
  [ttFiber8StateAt 0]

def ttFiber8Prefix1 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1]

def ttFiber8Prefix2 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2]

def ttFiber8Prefix3 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3]

def ttFiber8Prefix4 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4]

def ttFiber8Prefix5 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5]

def ttFiber8Prefix6 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6]

def ttFiber8Prefix7 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7]

def ttFiber8Prefix8 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8]

def ttFiber8Prefix9 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9]

def ttFiber8Prefix10 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10]

def ttFiber8Prefix11 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11]

def ttFiber8Prefix12 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12]

def ttFiber8Prefix13 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13]

def ttFiber8Prefix14 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14]

def ttFiber8Prefix15 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15]

def ttFiber8Prefix16 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16]

def ttFiber8Prefix17 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17]

def ttFiber8Prefix18 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18]

def ttFiber8Prefix19 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19]

def ttFiber8Prefix20 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20]

def ttFiber8Prefix21 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21]

def ttFiber8Prefix22 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22]

def ttFiber8Prefix23 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23]

def ttFiber8Prefix24 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24]

def ttFiber8Prefix25 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25]

def ttFiber8Prefix26 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26]

def ttFiber8Prefix27 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27]

def ttFiber8Prefix28 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28]

def ttFiber8Prefix29 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29]

def ttFiber8Prefix30 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30]

def ttFiber8Prefix31 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31]

def ttFiber8Prefix32 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32]

def ttFiber8Prefix33 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33]

def ttFiber8Prefix34 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34]

def ttFiber8Prefix35 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35]

def ttFiber8Prefix36 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36]

def ttFiber8Prefix37 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37]

def ttFiber8Prefix38 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38]

def ttFiber8Prefix39 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39]

def ttFiber8Prefix40 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40]

def ttFiber8Prefix41 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41]

def ttFiber8Prefix42 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42]

def ttFiber8Prefix43 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43]

def ttFiber8Prefix44 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44]

def ttFiber8Prefix45 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45]

def ttFiber8Prefix46 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46]

def ttFiber8Prefix47 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47]

def ttFiber8Prefix48 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48]

def ttFiber8Prefix49 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49]

def ttFiber8Prefix50 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50]

def ttFiber8Prefix51 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51]

def ttFiber8Prefix52 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52]

def ttFiber8Prefix53 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53]

def ttFiber8Prefix54 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54]

def ttFiber8Prefix55 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55]

def ttFiber8Prefix56 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56]

def ttFiber8Prefix57 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57]

def ttFiber8Prefix58 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58]

def ttFiber8Prefix59 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59]

def ttFiber8Prefix60 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60]

def ttFiber8Prefix61 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61]

def ttFiber8Prefix62 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62]

def ttFiber8Prefix63 : List (List TauState) :=
  [ttFiber8StateAt 0, ttFiber8StateAt 1, ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]

theorem ttFiber8ReverseRow_1_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk0] at h
  exact h.2

theorem ttFiber8ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 1)
      (ttFiber8RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 1) (by decide) ttFiber8ReverseRow_1_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_2_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk1] at h
  exact h.1

theorem ttFiber8ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 2)
      (ttFiber8RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 2) (by decide) ttFiber8ReverseRow_2_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_3_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk1] at h
  exact h.2

theorem ttFiber8ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 3)
      (ttFiber8RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 3) (by decide) ttFiber8ReverseRow_3_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_4_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk2] at h
  exact h.1

theorem ttFiber8ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 4)
      (ttFiber8RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 4) (by decide) ttFiber8ReverseRow_4_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_5_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk2] at h
  exact h.2

theorem ttFiber8ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 5)
      (ttFiber8RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 5) (by decide) ttFiber8ReverseRow_5_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_6_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk3] at h
  exact h.1

theorem ttFiber8ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 6)
      (ttFiber8RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 6) (by decide) ttFiber8ReverseRow_6_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_7_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk3] at h
  exact h.2

theorem ttFiber8ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 7)
      (ttFiber8RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 7) (by decide) ttFiber8ReverseRow_7_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_8_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk4] at h
  exact h.1

theorem ttFiber8ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 8)
      (ttFiber8RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 8) (by decide) ttFiber8ReverseRow_8_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_9_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk4] at h
  exact h.2

theorem ttFiber8ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 9)
      (ttFiber8RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 9) (by decide) ttFiber8ReverseRow_9_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_10_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk5] at h
  exact h.1

theorem ttFiber8ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 10)
      (ttFiber8RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 10) (by decide) ttFiber8ReverseRow_10_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_11_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk5] at h
  exact h.2

theorem ttFiber8ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 11)
      (ttFiber8RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 11) (by decide) ttFiber8ReverseRow_11_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_12_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk6] at h
  exact h.1

theorem ttFiber8ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 12)
      (ttFiber8RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 12) (by decide) ttFiber8ReverseRow_12_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_13_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk6] at h
  exact h.2

theorem ttFiber8ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 13)
      (ttFiber8RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 13) (by decide) ttFiber8ReverseRow_13_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_14_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk7] at h
  exact h.1

theorem ttFiber8ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 6) (ttFiber8StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 6) (ttFiber8StateAt 14)
      (ttFiber8RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 14) (by decide) ttFiber8ReverseRow_14_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_15_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk7] at h
  exact h.2

theorem ttFiber8ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 7) (ttFiber8StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 7) (ttFiber8StateAt 15)
      (ttFiber8RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 15) (by decide) ttFiber8ReverseRow_15_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_16_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk8] at h
  exact h.1

theorem ttFiber8ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 20) (ttFiber8StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 20) (ttFiber8StateAt 16)
      (ttFiber8RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 16) (by decide) ttFiber8ReverseRow_16_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_17_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk8] at h
  exact h.2

theorem ttFiber8ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 21) (ttFiber8StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 21) (ttFiber8StateAt 17)
      (ttFiber8RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 17) (by decide) ttFiber8ReverseRow_17_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_18_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk9] at h
  exact h.1

theorem ttFiber8ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 12) (ttFiber8StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 12) (ttFiber8StateAt 18)
      (ttFiber8RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 18) (by decide) ttFiber8ReverseRow_18_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_19_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk9] at h
  exact h.2

theorem ttFiber8ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 13) (ttFiber8StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 13) (ttFiber8StateAt 19)
      (ttFiber8RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 19) (by decide) ttFiber8ReverseRow_19_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_20_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk10] at h
  exact h.1

theorem ttFiber8ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 8) (ttFiber8StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 8) (ttFiber8StateAt 20)
      (ttFiber8RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 20) (by decide) ttFiber8ReverseRow_20_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_21_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk10] at h
  exact h.2

theorem ttFiber8ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 9) (ttFiber8StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 9) (ttFiber8StateAt 21)
      (ttFiber8RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 21) (by decide) ttFiber8ReverseRow_21_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_22_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk11] at h
  exact h.1

theorem ttFiber8ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 10) (ttFiber8StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 10) (ttFiber8StateAt 22)
      (ttFiber8RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 22) (by decide) ttFiber8ReverseRow_22_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_23_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk11] at h
  exact h.2

theorem ttFiber8ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 11) (ttFiber8StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 11) (ttFiber8StateAt 23)
      (ttFiber8RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 23) (by decide) ttFiber8ReverseRow_23_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_24_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk12] at h
  exact h.1

theorem ttFiber8ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 28) (ttFiber8StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 28) (ttFiber8StateAt 24)
      (ttFiber8RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 24) (by decide) ttFiber8ReverseRow_24_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_25_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk12] at h
  exact h.2

theorem ttFiber8ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 29) (ttFiber8StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 29) (ttFiber8StateAt 25)
      (ttFiber8RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 25) (by decide) ttFiber8ReverseRow_25_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_26_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk13] at h
  exact h.1

theorem ttFiber8ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 26)
      (ttFiber8RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 26) (by decide) ttFiber8ReverseRow_26_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_27_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk13] at h
  exact h.2

theorem ttFiber8ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 27)
      (ttFiber8RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 27) (by decide) ttFiber8ReverseRow_27_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_28_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk14] at h
  exact h.1

theorem ttFiber8ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 28)
      (ttFiber8RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 28) (by decide) ttFiber8ReverseRow_28_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_29_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk14] at h
  exact h.2

theorem ttFiber8ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 29)
      (ttFiber8RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 29) (by decide) ttFiber8ReverseRow_29_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_30_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk15] at h
  exact h.1

theorem ttFiber8ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 30)
      (ttFiber8RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 30) (by decide) ttFiber8ReverseRow_30_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_31_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk15] at h
  exact h.2

theorem ttFiber8ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 31)
      (ttFiber8RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 31) (by decide) ttFiber8ReverseRow_31_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_32_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk16] at h
  exact h.1

theorem ttFiber8ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 0) (ttFiber8StateAt 32)
      (ttFiber8RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 32) (by decide) ttFiber8ReverseRow_32_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_33_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk16] at h
  exact h.2

theorem ttFiber8ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 1) (ttFiber8StateAt 33)
      (ttFiber8RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 33) (by decide) ttFiber8ReverseRow_33_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_34_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk17] at h
  exact h.1

theorem ttFiber8ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 2) (ttFiber8StateAt 34)
      (ttFiber8RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 34) (by decide) ttFiber8ReverseRow_34_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_35_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk17] at h
  exact h.2

theorem ttFiber8ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 3) (ttFiber8StateAt 35)
      (ttFiber8RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 35) (by decide) ttFiber8ReverseRow_35_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_36_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk18] at h
  exact h.1

theorem ttFiber8ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 4) (ttFiber8StateAt 36)
      (ttFiber8RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 36) (by decide) ttFiber8ReverseRow_36_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_37_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk18] at h
  exact h.2

theorem ttFiber8ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 5) (ttFiber8StateAt 37)
      (ttFiber8RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 37) (by decide) ttFiber8ReverseRow_37_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_38_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk19] at h
  exact h.1

theorem ttFiber8ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 6) (ttFiber8StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 6) (ttFiber8StateAt 38)
      (ttFiber8RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 38) (by decide) ttFiber8ReverseRow_38_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_39_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk19] at h
  exact h.2

theorem ttFiber8ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 7) (ttFiber8StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 7) (ttFiber8StateAt 39)
      (ttFiber8RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 39) (by decide) ttFiber8ReverseRow_39_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_40_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk20] at h
  exact h.1

theorem ttFiber8ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 8) (ttFiber8StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 8) (ttFiber8StateAt 40)
      (ttFiber8RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 40) (by decide) ttFiber8ReverseRow_40_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_41_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk20] at h
  exact h.2

theorem ttFiber8ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 9) (ttFiber8StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 9) (ttFiber8StateAt 41)
      (ttFiber8RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 41) (by decide) ttFiber8ReverseRow_41_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_42_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk21] at h
  exact h.1

theorem ttFiber8ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 10) (ttFiber8StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 10) (ttFiber8StateAt 42)
      (ttFiber8RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 42) (by decide) ttFiber8ReverseRow_42_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_43_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk21] at h
  exact h.2

theorem ttFiber8ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 11) (ttFiber8StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 11) (ttFiber8StateAt 43)
      (ttFiber8RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 43) (by decide) ttFiber8ReverseRow_43_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_44_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk22] at h
  exact h.1

theorem ttFiber8ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 12) (ttFiber8StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 12) (ttFiber8StateAt 44)
      (ttFiber8RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 44) (by decide) ttFiber8ReverseRow_44_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_45_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk22] at h
  exact h.2

theorem ttFiber8ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 13) (ttFiber8StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 13) (ttFiber8StateAt 45)
      (ttFiber8RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 45) (by decide) ttFiber8ReverseRow_45_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_46_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk23] at h
  exact h.1

theorem ttFiber8ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 14) (ttFiber8StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 14) (ttFiber8StateAt 46)
      (ttFiber8RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 46) (by decide) ttFiber8ReverseRow_46_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_47_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk23] at h
  exact h.2

theorem ttFiber8ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 15) (ttFiber8StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 15) (ttFiber8StateAt 47)
      (ttFiber8RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 47) (by decide) ttFiber8ReverseRow_47_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_48_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk24] at h
  exact h.1

theorem ttFiber8ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 32) (ttFiber8StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 32) (ttFiber8StateAt 48)
      (ttFiber8RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 48) (by decide) ttFiber8ReverseRow_48_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_49_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk24] at h
  exact h.2

theorem ttFiber8ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 33) (ttFiber8StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 33) (ttFiber8StateAt 49)
      (ttFiber8RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 49) (by decide) ttFiber8ReverseRow_49_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_50_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk25] at h
  exact h.1

theorem ttFiber8ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 48) (ttFiber8StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 48) (ttFiber8StateAt 50)
      (ttFiber8RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 50) (by decide) ttFiber8ReverseRow_50_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_51_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk25] at h
  exact h.2

theorem ttFiber8ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 35) (ttFiber8StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 35) (ttFiber8StateAt 51)
      (ttFiber8RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 51) (by decide) ttFiber8ReverseRow_51_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_52_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk26] at h
  exact h.1

theorem ttFiber8ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 36) (ttFiber8StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 36) (ttFiber8StateAt 52)
      (ttFiber8RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 52) (by decide) ttFiber8ReverseRow_52_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_53_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk26] at h
  exact h.2

theorem ttFiber8ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 37) (ttFiber8StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 37) (ttFiber8StateAt 53)
      (ttFiber8RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 53) (by decide) ttFiber8ReverseRow_53_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_54_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk27] at h
  exact h.1

theorem ttFiber8ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 49) (ttFiber8StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 49) (ttFiber8StateAt 54)
      (ttFiber8RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 54) (by decide) ttFiber8ReverseRow_54_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_55_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk27] at h
  exact h.2

theorem ttFiber8ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 48) (ttFiber8StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 48) (ttFiber8StateAt 55)
      (ttFiber8RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 55) (by decide) ttFiber8ReverseRow_55_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_56_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk28] at h
  exact h.1

theorem ttFiber8ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 40) (ttFiber8StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 40) (ttFiber8StateAt 56)
      (ttFiber8RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 56) (by decide) ttFiber8ReverseRow_56_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_57_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk28] at h
  exact h.2

theorem ttFiber8ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 41) (ttFiber8StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 41) (ttFiber8StateAt 57)
      (ttFiber8RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 57) (by decide) ttFiber8ReverseRow_57_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_58_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk29] at h
  exact h.1

theorem ttFiber8ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 26) (ttFiber8StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 26) (ttFiber8StateAt 58)
      (ttFiber8RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 58) (by decide) ttFiber8ReverseRow_58_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_59_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk29] at h
  exact h.2

theorem ttFiber8ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 27) (ttFiber8StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 27) (ttFiber8StateAt 59)
      (ttFiber8RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 59) (by decide) ttFiber8ReverseRow_59_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_60_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk30] at h
  exact h.1

theorem ttFiber8ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 28) (ttFiber8StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 28) (ttFiber8StateAt 60)
      (ttFiber8RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 60) (by decide) ttFiber8ReverseRow_60_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_61_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk30] at h
  exact h.2

theorem ttFiber8ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 29) (ttFiber8StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 29) (ttFiber8StateAt 61)
      (ttFiber8RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 61) (by decide) ttFiber8ReverseRow_61_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_62_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk31] at h
  exact h.1

theorem ttFiber8ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 60) (ttFiber8StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 60) (ttFiber8StateAt 62)
      (ttFiber8RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 62) (by decide) ttFiber8ReverseRow_62_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8ReverseRow_63_ok' :
    directRowReverseValid ttFiber8Key ttFiber8Expected (ttFiber8RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber8Chunk31] at h
  exact h.2

theorem ttFiber8ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber8StateAt 31) (ttFiber8StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber8StateAt 31) (ttFiber8StateAt 63)
      (ttFiber8RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber8Key ttFiber8Expected
      (ttFiber8RowAt 63) (by decide) ttFiber8ReverseRow_63_ok'
    simpa [ttFiber8StateAt, ttFiber8RowAt, ttFiber8Rows, listGetD, directRow] using h

theorem ttFiber8FirstPassGrows :
    ((chainClosureStep ttWord ttFiber8DirectStates [ttFiber8StateAt 0]).length ==
      [ttFiber8StateAt 0].length) = false := by
  have hroot : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8DirectStates [ttFiber8StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber8DirectStates [ttFiber8StateAt 0]
      (ttFiber8StateAt 0) (by simp)
  have hnew : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8DirectStates [ttFiber8StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber8DirectStates [ttFiber8StateAt 0]
      (ttFiber8StateAt 0) (ttFiber8StateAt 1) (by decide) (by simp)
      ttFiber8ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber8DirectStates [ttFiber8StateAt 0])
    (ttFiber8StateAt 0) (ttFiber8StateAt 1) hroot hnew (by decide)

theorem ttFiber8State0_in_pass0_full :
    ttFiber8StateAt 0 ∈ [ttFiber8StateAt 0] := by
  simp

theorem ttFiber8State0_in_pass1_full :
    ttFiber8StateAt 0 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber8DirectStates
    ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full

theorem ttFiber8State1_in_pass1_prefix1 :
    ttFiber8StateAt 1 ∈ chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix0 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix0
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix1 = ttFiber8Prefix0 ++ [ttFiber8StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 1) []
    (chainClosureStep ttWord ttFiber8Prefix0 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep1

theorem ttFiber8State1_in_pass1_full :
    ttFiber8StateAt 1 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix1 ++ [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1

theorem ttFiber8State2_in_pass1_prefix2 :
    ttFiber8StateAt 2 ∈ chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix1 = ttFiber8Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1
  rw [show ttFiber8Prefix2 = ttFiber8Prefix1 ++ [ttFiber8StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 2) []
    (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) hparentBefore ttFiber8ReverseSingleStep2

theorem ttFiber8State2_in_pass1_full :
    ttFiber8StateAt 2 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix2 ++ [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 2) ttFiber8State2_in_pass1_prefix2

theorem ttFiber8State3_in_pass1_prefix3 :
    ttFiber8StateAt 3 ∈ chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix2
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix3 = ttFiber8Prefix2 ++ [ttFiber8StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 3) []
    (chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep3

theorem ttFiber8State3_in_pass1_full :
    ttFiber8StateAt 3 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix3 ++ [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 3) ttFiber8State3_in_pass1_prefix3

theorem ttFiber8State4_in_pass1_prefix4 :
    ttFiber8StateAt 4 ∈ chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix3
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix4 = ttFiber8Prefix3 ++ [ttFiber8StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 4) []
    (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep4

theorem ttFiber8State4_in_pass1_full :
    ttFiber8StateAt 4 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix4 ++ [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 4) ttFiber8State4_in_pass1_prefix4

theorem ttFiber8State5_in_pass1_prefix5 :
    ttFiber8StateAt 5 ∈ chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix4 = ttFiber8Prefix1 ++ [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4]
      (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1
  rw [show ttFiber8Prefix5 = ttFiber8Prefix4 ++ [ttFiber8StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 5) []
    (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) hparentBefore ttFiber8ReverseSingleStep5

theorem ttFiber8State5_in_pass1_full :
    ttFiber8StateAt 5 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix5 ++ [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 5) ttFiber8State5_in_pass1_prefix5

theorem ttFiber8State6_in_pass1_prefix6 :
    ttFiber8StateAt 6 ∈ chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 4 ∈
      chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix5 = ttFiber8Prefix4 ++ [ttFiber8StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 5]
      (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 4) ttFiber8State4_in_pass1_prefix4
  rw [show ttFiber8Prefix6 = ttFiber8Prefix5 ++ [ttFiber8StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 6) []
    (chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 4) hparentBefore ttFiber8ReverseSingleStep6

theorem ttFiber8State6_in_pass1_full :
    ttFiber8StateAt 6 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix6 ++ [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 6) ttFiber8State6_in_pass1_prefix6

theorem ttFiber8State7_in_pass1_prefix7 :
    ttFiber8StateAt 7 ∈ chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 3 ∈
      chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix6 = ttFiber8Prefix3 ++ [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6]
      (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 3) ttFiber8State3_in_pass1_prefix3
  rw [show ttFiber8Prefix7 = ttFiber8Prefix6 ++ [ttFiber8StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 7) []
    (chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 3) hparentBefore ttFiber8ReverseSingleStep7

theorem ttFiber8State7_in_pass1_full :
    ttFiber8StateAt 7 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix7 ++ [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 7) ttFiber8State7_in_pass1_prefix7

theorem ttFiber8State8_in_pass1_prefix8 :
    ttFiber8StateAt 8 ∈ chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix7
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix8 = ttFiber8Prefix7 ++ [ttFiber8StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 8) []
    (chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep8

theorem ttFiber8State8_in_pass1_full :
    ttFiber8StateAt 8 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix8 ++ [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 8) ttFiber8State8_in_pass1_prefix8

theorem ttFiber8State9_in_pass1_prefix9 :
    ttFiber8StateAt 9 ∈ chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix8 = ttFiber8Prefix1 ++ [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8]
      (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1
  rw [show ttFiber8Prefix9 = ttFiber8Prefix8 ++ [ttFiber8StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 9) []
    (chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) hparentBefore ttFiber8ReverseSingleStep9

theorem ttFiber8State9_in_pass1_full :
    ttFiber8StateAt 9 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix9 ++ [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 9) ttFiber8State9_in_pass1_prefix9

theorem ttFiber8State10_in_pass1_prefix10 :
    ttFiber8StateAt 10 ∈ chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 2 ∈
      chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix9 = ttFiber8Prefix2 ++ [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9]
      (chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 2) ttFiber8State2_in_pass1_prefix2
  rw [show ttFiber8Prefix10 = ttFiber8Prefix9 ++ [ttFiber8StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 10) []
    (chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 2) hparentBefore ttFiber8ReverseSingleStep10

theorem ttFiber8State10_in_pass1_full :
    ttFiber8StateAt 10 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix10 ++ [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 10) ttFiber8State10_in_pass1_prefix10

theorem ttFiber8State11_in_pass1_prefix11 :
    ttFiber8StateAt 11 ∈ chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 3 ∈
      chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix10 = ttFiber8Prefix3 ++ [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10]
      (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 3) ttFiber8State3_in_pass1_prefix3
  rw [show ttFiber8Prefix11 = ttFiber8Prefix10 ++ [ttFiber8StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 11) []
    (chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 3) hparentBefore ttFiber8ReverseSingleStep11

theorem ttFiber8State11_in_pass1_full :
    ttFiber8StateAt 11 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix11 ++ [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 11) ttFiber8State11_in_pass1_prefix11

theorem ttFiber8State12_in_pass1_prefix12 :
    ttFiber8StateAt 12 ∈ chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 4 ∈
      chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix11 = ttFiber8Prefix4 ++ [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11]
      (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 4) ttFiber8State4_in_pass1_prefix4
  rw [show ttFiber8Prefix12 = ttFiber8Prefix11 ++ [ttFiber8StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 12) []
    (chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 4) hparentBefore ttFiber8ReverseSingleStep12

theorem ttFiber8State12_in_pass1_full :
    ttFiber8StateAt 12 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix12 ++ [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 12) ttFiber8State12_in_pass1_prefix12

theorem ttFiber8State13_in_pass1_prefix13 :
    ttFiber8StateAt 13 ∈ chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 5 ∈
      chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix12 = ttFiber8Prefix5 ++ [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12]
      (chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 5) ttFiber8State5_in_pass1_prefix5
  rw [show ttFiber8Prefix13 = ttFiber8Prefix12 ++ [ttFiber8StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 13) []
    (chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 5) hparentBefore ttFiber8ReverseSingleStep13

theorem ttFiber8State13_in_pass1_full :
    ttFiber8StateAt 13 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix13 ++ [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 13) ttFiber8State13_in_pass1_prefix13

theorem ttFiber8State14_in_pass1_prefix14 :
    ttFiber8StateAt 14 ∈ chainClosureStep ttWord ttFiber8Prefix14 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 6 ∈
      chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix13 = ttFiber8Prefix6 ++ [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13]
      (chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 6) ttFiber8State6_in_pass1_prefix6
  rw [show ttFiber8Prefix14 = ttFiber8Prefix13 ++ [ttFiber8StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 14) []
    (chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 6) hparentBefore ttFiber8ReverseSingleStep14

theorem ttFiber8State14_in_pass1_full :
    ttFiber8StateAt 14 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix14 ++ [ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix14 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 14) ttFiber8State14_in_pass1_prefix14

theorem ttFiber8State15_in_pass1_prefix15 :
    ttFiber8StateAt 15 ∈ chainClosureStep ttWord ttFiber8Prefix15 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 7 ∈
      chainClosureStep ttWord ttFiber8Prefix14 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix14 = ttFiber8Prefix7 ++ [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14]
      (chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 7) ttFiber8State7_in_pass1_prefix7
  rw [show ttFiber8Prefix15 = ttFiber8Prefix14 ++ [ttFiber8StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 15) []
    (chainClosureStep ttWord ttFiber8Prefix14 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 7) hparentBefore ttFiber8ReverseSingleStep15

theorem ttFiber8State15_in_pass1_full :
    ttFiber8StateAt 15 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix15 ++ [ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix15 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 15) ttFiber8State15_in_pass1_prefix15

theorem ttFiber8State18_in_pass1_prefix18 :
    ttFiber8StateAt 18 ∈ chainClosureStep ttWord ttFiber8Prefix18 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 12 ∈
      chainClosureStep ttWord ttFiber8Prefix17 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix17 = ttFiber8Prefix12 ++ [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17]
      (chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 12) ttFiber8State12_in_pass1_prefix12
  rw [show ttFiber8Prefix18 = ttFiber8Prefix17 ++ [ttFiber8StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 18) []
    (chainClosureStep ttWord ttFiber8Prefix17 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 12) hparentBefore ttFiber8ReverseSingleStep18

theorem ttFiber8State18_in_pass1_full :
    ttFiber8StateAt 18 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix18 ++ [ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix18 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 18) ttFiber8State18_in_pass1_prefix18

theorem ttFiber8State19_in_pass1_prefix19 :
    ttFiber8StateAt 19 ∈ chainClosureStep ttWord ttFiber8Prefix19 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 13 ∈
      chainClosureStep ttWord ttFiber8Prefix18 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix18 = ttFiber8Prefix13 ++ [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18]
      (chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 13) ttFiber8State13_in_pass1_prefix13
  rw [show ttFiber8Prefix19 = ttFiber8Prefix18 ++ [ttFiber8StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 19) []
    (chainClosureStep ttWord ttFiber8Prefix18 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 13) hparentBefore ttFiber8ReverseSingleStep19

theorem ttFiber8State19_in_pass1_full :
    ttFiber8StateAt 19 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix19 ++ [ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix19 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 19) ttFiber8State19_in_pass1_prefix19

theorem ttFiber8State20_in_pass1_prefix20 :
    ttFiber8StateAt 20 ∈ chainClosureStep ttWord ttFiber8Prefix20 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 8 ∈
      chainClosureStep ttWord ttFiber8Prefix19 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix19 = ttFiber8Prefix8 ++ [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19]
      (chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 8) ttFiber8State8_in_pass1_prefix8
  rw [show ttFiber8Prefix20 = ttFiber8Prefix19 ++ [ttFiber8StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 20) []
    (chainClosureStep ttWord ttFiber8Prefix19 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 8) hparentBefore ttFiber8ReverseSingleStep20

theorem ttFiber8State20_in_pass1_full :
    ttFiber8StateAt 20 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix20 ++ [ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix20 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 20) ttFiber8State20_in_pass1_prefix20

theorem ttFiber8State21_in_pass1_prefix21 :
    ttFiber8StateAt 21 ∈ chainClosureStep ttWord ttFiber8Prefix21 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 9 ∈
      chainClosureStep ttWord ttFiber8Prefix20 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix20 = ttFiber8Prefix9 ++ [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20]
      (chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 9) ttFiber8State9_in_pass1_prefix9
  rw [show ttFiber8Prefix21 = ttFiber8Prefix20 ++ [ttFiber8StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 21) []
    (chainClosureStep ttWord ttFiber8Prefix20 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 9) hparentBefore ttFiber8ReverseSingleStep21

theorem ttFiber8State21_in_pass1_full :
    ttFiber8StateAt 21 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix21 ++ [ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix21 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 21) ttFiber8State21_in_pass1_prefix21

theorem ttFiber8State22_in_pass1_prefix22 :
    ttFiber8StateAt 22 ∈ chainClosureStep ttWord ttFiber8Prefix22 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 10 ∈
      chainClosureStep ttWord ttFiber8Prefix21 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix21 = ttFiber8Prefix10 ++ [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21]
      (chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 10) ttFiber8State10_in_pass1_prefix10
  rw [show ttFiber8Prefix22 = ttFiber8Prefix21 ++ [ttFiber8StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 22) []
    (chainClosureStep ttWord ttFiber8Prefix21 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 10) hparentBefore ttFiber8ReverseSingleStep22

theorem ttFiber8State22_in_pass1_full :
    ttFiber8StateAt 22 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix22 ++ [ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix22 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 22) ttFiber8State22_in_pass1_prefix22

theorem ttFiber8State23_in_pass1_prefix23 :
    ttFiber8StateAt 23 ∈ chainClosureStep ttWord ttFiber8Prefix23 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 11 ∈
      chainClosureStep ttWord ttFiber8Prefix22 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix22 = ttFiber8Prefix11 ++ [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22]
      (chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 11) ttFiber8State11_in_pass1_prefix11
  rw [show ttFiber8Prefix23 = ttFiber8Prefix22 ++ [ttFiber8StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 23) []
    (chainClosureStep ttWord ttFiber8Prefix22 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 11) hparentBefore ttFiber8ReverseSingleStep23

theorem ttFiber8State23_in_pass1_full :
    ttFiber8StateAt 23 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix23 ++ [ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix23 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 23) ttFiber8State23_in_pass1_prefix23

theorem ttFiber8State26_in_pass1_prefix26 :
    ttFiber8StateAt 26 ∈ chainClosureStep ttWord ttFiber8Prefix26 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 4 ∈
      chainClosureStep ttWord ttFiber8Prefix25 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix25 = ttFiber8Prefix4 ++ [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25]
      (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 4) ttFiber8State4_in_pass1_prefix4
  rw [show ttFiber8Prefix26 = ttFiber8Prefix25 ++ [ttFiber8StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 26) []
    (chainClosureStep ttWord ttFiber8Prefix25 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 4) hparentBefore ttFiber8ReverseSingleStep26

theorem ttFiber8State26_in_pass1_full :
    ttFiber8StateAt 26 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix26 ++ [ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix26 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 26) ttFiber8State26_in_pass1_prefix26

theorem ttFiber8State27_in_pass1_prefix27 :
    ttFiber8StateAt 27 ∈ chainClosureStep ttWord ttFiber8Prefix27 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 5 ∈
      chainClosureStep ttWord ttFiber8Prefix26 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix26 = ttFiber8Prefix5 ++ [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26]
      (chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 5) ttFiber8State5_in_pass1_prefix5
  rw [show ttFiber8Prefix27 = ttFiber8Prefix26 ++ [ttFiber8StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 27) []
    (chainClosureStep ttWord ttFiber8Prefix26 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 5) hparentBefore ttFiber8ReverseSingleStep27

theorem ttFiber8State27_in_pass1_full :
    ttFiber8StateAt 27 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix27 ++ [ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix27 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 27) ttFiber8State27_in_pass1_prefix27

theorem ttFiber8State28_in_pass1_prefix28 :
    ttFiber8StateAt 28 ∈ chainClosureStep ttWord ttFiber8Prefix28 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix27 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix27
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix28 = ttFiber8Prefix27 ++ [ttFiber8StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 28) []
    (chainClosureStep ttWord ttFiber8Prefix27 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep28

theorem ttFiber8State28_in_pass1_full :
    ttFiber8StateAt 28 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix28 ++ [ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix28 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 28) ttFiber8State28_in_pass1_prefix28

theorem ttFiber8State29_in_pass1_prefix29 :
    ttFiber8StateAt 29 ∈ chainClosureStep ttWord ttFiber8Prefix29 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8Prefix28 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix28 = ttFiber8Prefix1 ++ [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28]
      (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1
  rw [show ttFiber8Prefix29 = ttFiber8Prefix28 ++ [ttFiber8StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 29) []
    (chainClosureStep ttWord ttFiber8Prefix28 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) hparentBefore ttFiber8ReverseSingleStep29

theorem ttFiber8State29_in_pass1_full :
    ttFiber8StateAt 29 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix29 ++ [ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix29 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 29) ttFiber8State29_in_pass1_prefix29

theorem ttFiber8State30_in_pass1_prefix30 :
    ttFiber8StateAt 30 ∈ chainClosureStep ttWord ttFiber8Prefix30 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 2 ∈
      chainClosureStep ttWord ttFiber8Prefix29 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix29 = ttFiber8Prefix2 ++ [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29]
      (chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 2) ttFiber8State2_in_pass1_prefix2
  rw [show ttFiber8Prefix30 = ttFiber8Prefix29 ++ [ttFiber8StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 30) []
    (chainClosureStep ttWord ttFiber8Prefix29 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 2) hparentBefore ttFiber8ReverseSingleStep30

theorem ttFiber8State30_in_pass1_full :
    ttFiber8StateAt 30 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix30 ++ [ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix30 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 30) ttFiber8State30_in_pass1_prefix30

theorem ttFiber8State31_in_pass1_prefix31 :
    ttFiber8StateAt 31 ∈ chainClosureStep ttWord ttFiber8Prefix31 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 3 ∈
      chainClosureStep ttWord ttFiber8Prefix30 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix30 = ttFiber8Prefix3 ++ [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30]
      (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 3) ttFiber8State3_in_pass1_prefix3
  rw [show ttFiber8Prefix31 = ttFiber8Prefix30 ++ [ttFiber8StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 31) []
    (chainClosureStep ttWord ttFiber8Prefix30 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 3) hparentBefore ttFiber8ReverseSingleStep31

theorem ttFiber8State31_in_pass1_full :
    ttFiber8StateAt 31 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix31 ++ [ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix31 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 31) ttFiber8State31_in_pass1_prefix31

theorem ttFiber8State32_in_pass1_prefix32 :
    ttFiber8StateAt 32 ∈ chainClosureStep ttWord ttFiber8Prefix32 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 0 ∈
      chainClosureStep ttWord ttFiber8Prefix31 ([ttFiber8StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix31
      ([ttFiber8StateAt 0]) (ttFiber8StateAt 0) ttFiber8State0_in_pass0_full
  rw [show ttFiber8Prefix32 = ttFiber8Prefix31 ++ [ttFiber8StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 32) []
    (chainClosureStep ttWord ttFiber8Prefix31 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 0) hparentBefore ttFiber8ReverseSingleStep32

theorem ttFiber8State32_in_pass1_full :
    ttFiber8StateAt 32 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix32 ++ [ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix32 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 32) ttFiber8State32_in_pass1_prefix32

theorem ttFiber8State33_in_pass1_prefix33 :
    ttFiber8StateAt 33 ∈ chainClosureStep ttWord ttFiber8Prefix33 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 1 ∈
      chainClosureStep ttWord ttFiber8Prefix32 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix32 = ttFiber8Prefix1 ++ [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 2, ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32]
      (chainClosureStep ttWord ttFiber8Prefix1 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 1) ttFiber8State1_in_pass1_prefix1
  rw [show ttFiber8Prefix33 = ttFiber8Prefix32 ++ [ttFiber8StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 33) []
    (chainClosureStep ttWord ttFiber8Prefix32 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 1) hparentBefore ttFiber8ReverseSingleStep33

theorem ttFiber8State33_in_pass1_full :
    ttFiber8StateAt 33 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix33 ++ [ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix33 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 33) ttFiber8State33_in_pass1_prefix33

theorem ttFiber8State34_in_pass1_prefix34 :
    ttFiber8StateAt 34 ∈ chainClosureStep ttWord ttFiber8Prefix34 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 2 ∈
      chainClosureStep ttWord ttFiber8Prefix33 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix33 = ttFiber8Prefix2 ++ [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 3, ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33]
      (chainClosureStep ttWord ttFiber8Prefix2 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 2) ttFiber8State2_in_pass1_prefix2
  rw [show ttFiber8Prefix34 = ttFiber8Prefix33 ++ [ttFiber8StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 34) []
    (chainClosureStep ttWord ttFiber8Prefix33 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 2) hparentBefore ttFiber8ReverseSingleStep34

theorem ttFiber8State34_in_pass1_full :
    ttFiber8StateAt 34 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix34 ++ [ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix34 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 34) ttFiber8State34_in_pass1_prefix34

theorem ttFiber8State35_in_pass1_prefix35 :
    ttFiber8StateAt 35 ∈ chainClosureStep ttWord ttFiber8Prefix35 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 3 ∈
      chainClosureStep ttWord ttFiber8Prefix34 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix34 = ttFiber8Prefix3 ++ [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 4, ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34]
      (chainClosureStep ttWord ttFiber8Prefix3 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 3) ttFiber8State3_in_pass1_prefix3
  rw [show ttFiber8Prefix35 = ttFiber8Prefix34 ++ [ttFiber8StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 35) []
    (chainClosureStep ttWord ttFiber8Prefix34 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 3) hparentBefore ttFiber8ReverseSingleStep35

theorem ttFiber8State35_in_pass1_full :
    ttFiber8StateAt 35 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix35 ++ [ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix35 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 35) ttFiber8State35_in_pass1_prefix35

theorem ttFiber8State36_in_pass1_prefix36 :
    ttFiber8StateAt 36 ∈ chainClosureStep ttWord ttFiber8Prefix36 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 4 ∈
      chainClosureStep ttWord ttFiber8Prefix35 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix35 = ttFiber8Prefix4 ++ [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 5, ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35]
      (chainClosureStep ttWord ttFiber8Prefix4 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 4) ttFiber8State4_in_pass1_prefix4
  rw [show ttFiber8Prefix36 = ttFiber8Prefix35 ++ [ttFiber8StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 36) []
    (chainClosureStep ttWord ttFiber8Prefix35 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 4) hparentBefore ttFiber8ReverseSingleStep36

theorem ttFiber8State36_in_pass1_full :
    ttFiber8StateAt 36 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix36 ++ [ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix36 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 36) ttFiber8State36_in_pass1_prefix36

theorem ttFiber8State37_in_pass1_prefix37 :
    ttFiber8StateAt 37 ∈ chainClosureStep ttWord ttFiber8Prefix37 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 5 ∈
      chainClosureStep ttWord ttFiber8Prefix36 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix36 = ttFiber8Prefix5 ++ [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 6, ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36]
      (chainClosureStep ttWord ttFiber8Prefix5 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 5) ttFiber8State5_in_pass1_prefix5
  rw [show ttFiber8Prefix37 = ttFiber8Prefix36 ++ [ttFiber8StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 37) []
    (chainClosureStep ttWord ttFiber8Prefix36 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 5) hparentBefore ttFiber8ReverseSingleStep37

theorem ttFiber8State37_in_pass1_full :
    ttFiber8StateAt 37 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix37 ++ [ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix37 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 37) ttFiber8State37_in_pass1_prefix37

theorem ttFiber8State38_in_pass1_prefix38 :
    ttFiber8StateAt 38 ∈ chainClosureStep ttWord ttFiber8Prefix38 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 6 ∈
      chainClosureStep ttWord ttFiber8Prefix37 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix37 = ttFiber8Prefix6 ++ [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 7, ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37]
      (chainClosureStep ttWord ttFiber8Prefix6 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 6) ttFiber8State6_in_pass1_prefix6
  rw [show ttFiber8Prefix38 = ttFiber8Prefix37 ++ [ttFiber8StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 38) []
    (chainClosureStep ttWord ttFiber8Prefix37 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 6) hparentBefore ttFiber8ReverseSingleStep38

theorem ttFiber8State38_in_pass1_full :
    ttFiber8StateAt 38 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix38 ++ [ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix38 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 38) ttFiber8State38_in_pass1_prefix38

theorem ttFiber8State39_in_pass1_prefix39 :
    ttFiber8StateAt 39 ∈ chainClosureStep ttWord ttFiber8Prefix39 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 7 ∈
      chainClosureStep ttWord ttFiber8Prefix38 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix38 = ttFiber8Prefix7 ++ [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 8, ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38]
      (chainClosureStep ttWord ttFiber8Prefix7 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 7) ttFiber8State7_in_pass1_prefix7
  rw [show ttFiber8Prefix39 = ttFiber8Prefix38 ++ [ttFiber8StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 39) []
    (chainClosureStep ttWord ttFiber8Prefix38 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 7) hparentBefore ttFiber8ReverseSingleStep39

theorem ttFiber8State39_in_pass1_full :
    ttFiber8StateAt 39 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix39 ++ [ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix39 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 39) ttFiber8State39_in_pass1_prefix39

theorem ttFiber8State40_in_pass1_prefix40 :
    ttFiber8StateAt 40 ∈ chainClosureStep ttWord ttFiber8Prefix40 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 8 ∈
      chainClosureStep ttWord ttFiber8Prefix39 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix39 = ttFiber8Prefix8 ++ [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 9, ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39]
      (chainClosureStep ttWord ttFiber8Prefix8 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 8) ttFiber8State8_in_pass1_prefix8
  rw [show ttFiber8Prefix40 = ttFiber8Prefix39 ++ [ttFiber8StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 40) []
    (chainClosureStep ttWord ttFiber8Prefix39 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 8) hparentBefore ttFiber8ReverseSingleStep40

theorem ttFiber8State40_in_pass1_full :
    ttFiber8StateAt 40 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix40 ++ [ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix40 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 40) ttFiber8State40_in_pass1_prefix40

theorem ttFiber8State41_in_pass1_prefix41 :
    ttFiber8StateAt 41 ∈ chainClosureStep ttWord ttFiber8Prefix41 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 9 ∈
      chainClosureStep ttWord ttFiber8Prefix40 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix40 = ttFiber8Prefix9 ++ [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 10, ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40]
      (chainClosureStep ttWord ttFiber8Prefix9 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 9) ttFiber8State9_in_pass1_prefix9
  rw [show ttFiber8Prefix41 = ttFiber8Prefix40 ++ [ttFiber8StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 41) []
    (chainClosureStep ttWord ttFiber8Prefix40 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 9) hparentBefore ttFiber8ReverseSingleStep41

theorem ttFiber8State41_in_pass1_full :
    ttFiber8StateAt 41 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix41 ++ [ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix41 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 41) ttFiber8State41_in_pass1_prefix41

theorem ttFiber8State42_in_pass1_prefix42 :
    ttFiber8StateAt 42 ∈ chainClosureStep ttWord ttFiber8Prefix42 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 10 ∈
      chainClosureStep ttWord ttFiber8Prefix41 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix41 = ttFiber8Prefix10 ++ [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 11, ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41]
      (chainClosureStep ttWord ttFiber8Prefix10 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 10) ttFiber8State10_in_pass1_prefix10
  rw [show ttFiber8Prefix42 = ttFiber8Prefix41 ++ [ttFiber8StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 42) []
    (chainClosureStep ttWord ttFiber8Prefix41 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 10) hparentBefore ttFiber8ReverseSingleStep42

theorem ttFiber8State42_in_pass1_full :
    ttFiber8StateAt 42 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix42 ++ [ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix42 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 42) ttFiber8State42_in_pass1_prefix42

theorem ttFiber8State43_in_pass1_prefix43 :
    ttFiber8StateAt 43 ∈ chainClosureStep ttWord ttFiber8Prefix43 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 11 ∈
      chainClosureStep ttWord ttFiber8Prefix42 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix42 = ttFiber8Prefix11 ++ [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 12, ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42]
      (chainClosureStep ttWord ttFiber8Prefix11 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 11) ttFiber8State11_in_pass1_prefix11
  rw [show ttFiber8Prefix43 = ttFiber8Prefix42 ++ [ttFiber8StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 43) []
    (chainClosureStep ttWord ttFiber8Prefix42 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 11) hparentBefore ttFiber8ReverseSingleStep43

theorem ttFiber8State43_in_pass1_full :
    ttFiber8StateAt 43 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix43 ++ [ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix43 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 43) ttFiber8State43_in_pass1_prefix43

theorem ttFiber8State44_in_pass1_prefix44 :
    ttFiber8StateAt 44 ∈ chainClosureStep ttWord ttFiber8Prefix44 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 12 ∈
      chainClosureStep ttWord ttFiber8Prefix43 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix43 = ttFiber8Prefix12 ++ [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 13, ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43]
      (chainClosureStep ttWord ttFiber8Prefix12 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 12) ttFiber8State12_in_pass1_prefix12
  rw [show ttFiber8Prefix44 = ttFiber8Prefix43 ++ [ttFiber8StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 44) []
    (chainClosureStep ttWord ttFiber8Prefix43 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 12) hparentBefore ttFiber8ReverseSingleStep44

theorem ttFiber8State44_in_pass1_full :
    ttFiber8StateAt 44 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix44 ++ [ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix44 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 44) ttFiber8State44_in_pass1_prefix44

theorem ttFiber8State45_in_pass1_prefix45 :
    ttFiber8StateAt 45 ∈ chainClosureStep ttWord ttFiber8Prefix45 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 13 ∈
      chainClosureStep ttWord ttFiber8Prefix44 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix44 = ttFiber8Prefix13 ++ [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 14, ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44]
      (chainClosureStep ttWord ttFiber8Prefix13 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 13) ttFiber8State13_in_pass1_prefix13
  rw [show ttFiber8Prefix45 = ttFiber8Prefix44 ++ [ttFiber8StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 45) []
    (chainClosureStep ttWord ttFiber8Prefix44 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 13) hparentBefore ttFiber8ReverseSingleStep45

theorem ttFiber8State45_in_pass1_full :
    ttFiber8StateAt 45 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix45 ++ [ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix45 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 45) ttFiber8State45_in_pass1_prefix45

theorem ttFiber8State46_in_pass1_prefix46 :
    ttFiber8StateAt 46 ∈ chainClosureStep ttWord ttFiber8Prefix46 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 14 ∈
      chainClosureStep ttWord ttFiber8Prefix45 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix45 = ttFiber8Prefix14 ++ [ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 15, ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45]
      (chainClosureStep ttWord ttFiber8Prefix14 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 14) ttFiber8State14_in_pass1_prefix14
  rw [show ttFiber8Prefix46 = ttFiber8Prefix45 ++ [ttFiber8StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 46) []
    (chainClosureStep ttWord ttFiber8Prefix45 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 14) hparentBefore ttFiber8ReverseSingleStep46

theorem ttFiber8State46_in_pass1_full :
    ttFiber8StateAt 46 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix46 ++ [ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix46 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 46) ttFiber8State46_in_pass1_prefix46

theorem ttFiber8State47_in_pass1_prefix47 :
    ttFiber8StateAt 47 ∈ chainClosureStep ttWord ttFiber8Prefix47 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 15 ∈
      chainClosureStep ttWord ttFiber8Prefix46 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix46 = ttFiber8Prefix15 ++ [ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 16, ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46]
      (chainClosureStep ttWord ttFiber8Prefix15 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 15) ttFiber8State15_in_pass1_prefix15
  rw [show ttFiber8Prefix47 = ttFiber8Prefix46 ++ [ttFiber8StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 47) []
    (chainClosureStep ttWord ttFiber8Prefix46 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 15) hparentBefore ttFiber8ReverseSingleStep47

theorem ttFiber8State47_in_pass1_full :
    ttFiber8StateAt 47 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix47 ++ [ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix47 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 47) ttFiber8State47_in_pass1_prefix47

theorem ttFiber8State48_in_pass1_prefix48 :
    ttFiber8StateAt 48 ∈ chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 32 ∈
      chainClosureStep ttWord ttFiber8Prefix47 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix47 = ttFiber8Prefix32 ++ [ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47]
      (chainClosureStep ttWord ttFiber8Prefix32 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 32) ttFiber8State32_in_pass1_prefix32
  rw [show ttFiber8Prefix48 = ttFiber8Prefix47 ++ [ttFiber8StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 48) []
    (chainClosureStep ttWord ttFiber8Prefix47 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 32) hparentBefore ttFiber8ReverseSingleStep48

theorem ttFiber8State48_in_pass1_full :
    ttFiber8StateAt 48 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix48 ++ [ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 48) ttFiber8State48_in_pass1_prefix48

theorem ttFiber8State49_in_pass1_prefix49 :
    ttFiber8StateAt 49 ∈ chainClosureStep ttWord ttFiber8Prefix49 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 33 ∈
      chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix48 = ttFiber8Prefix33 ++ [ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48]
      (chainClosureStep ttWord ttFiber8Prefix33 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 33) ttFiber8State33_in_pass1_prefix33
  rw [show ttFiber8Prefix49 = ttFiber8Prefix48 ++ [ttFiber8StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 49) []
    (chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 33) hparentBefore ttFiber8ReverseSingleStep49

theorem ttFiber8State49_in_pass1_full :
    ttFiber8StateAt 49 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix49 ++ [ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix49 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 49) ttFiber8State49_in_pass1_prefix49

theorem ttFiber8State50_in_pass1_prefix50 :
    ttFiber8StateAt 50 ∈ chainClosureStep ttWord ttFiber8Prefix50 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 48 ∈
      chainClosureStep ttWord ttFiber8Prefix49 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix49 = ttFiber8Prefix48 ++ [ttFiber8StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 49]
      (chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 48) ttFiber8State48_in_pass1_prefix48
  rw [show ttFiber8Prefix50 = ttFiber8Prefix49 ++ [ttFiber8StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 50) []
    (chainClosureStep ttWord ttFiber8Prefix49 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 48) hparentBefore ttFiber8ReverseSingleStep50

theorem ttFiber8State50_in_pass1_full :
    ttFiber8StateAt 50 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix50 ++ [ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix50 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 50) ttFiber8State50_in_pass1_prefix50

theorem ttFiber8State51_in_pass1_prefix51 :
    ttFiber8StateAt 51 ∈ chainClosureStep ttWord ttFiber8Prefix51 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 35 ∈
      chainClosureStep ttWord ttFiber8Prefix50 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix50 = ttFiber8Prefix35 ++ [ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50]
      (chainClosureStep ttWord ttFiber8Prefix35 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 35) ttFiber8State35_in_pass1_prefix35
  rw [show ttFiber8Prefix51 = ttFiber8Prefix50 ++ [ttFiber8StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 51) []
    (chainClosureStep ttWord ttFiber8Prefix50 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 35) hparentBefore ttFiber8ReverseSingleStep51

theorem ttFiber8State51_in_pass1_full :
    ttFiber8StateAt 51 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix51 ++ [ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix51 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 51) ttFiber8State51_in_pass1_prefix51

theorem ttFiber8State52_in_pass1_prefix52 :
    ttFiber8StateAt 52 ∈ chainClosureStep ttWord ttFiber8Prefix52 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 36 ∈
      chainClosureStep ttWord ttFiber8Prefix51 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix51 = ttFiber8Prefix36 ++ [ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51]
      (chainClosureStep ttWord ttFiber8Prefix36 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 36) ttFiber8State36_in_pass1_prefix36
  rw [show ttFiber8Prefix52 = ttFiber8Prefix51 ++ [ttFiber8StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 52) []
    (chainClosureStep ttWord ttFiber8Prefix51 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 36) hparentBefore ttFiber8ReverseSingleStep52

theorem ttFiber8State52_in_pass1_full :
    ttFiber8StateAt 52 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix52 ++ [ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix52 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 52) ttFiber8State52_in_pass1_prefix52

theorem ttFiber8State53_in_pass1_prefix53 :
    ttFiber8StateAt 53 ∈ chainClosureStep ttWord ttFiber8Prefix53 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 37 ∈
      chainClosureStep ttWord ttFiber8Prefix52 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix52 = ttFiber8Prefix37 ++ [ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52]
      (chainClosureStep ttWord ttFiber8Prefix37 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 37) ttFiber8State37_in_pass1_prefix37
  rw [show ttFiber8Prefix53 = ttFiber8Prefix52 ++ [ttFiber8StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 53) []
    (chainClosureStep ttWord ttFiber8Prefix52 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 37) hparentBefore ttFiber8ReverseSingleStep53

theorem ttFiber8State53_in_pass1_full :
    ttFiber8StateAt 53 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix53 ++ [ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix53 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 53) ttFiber8State53_in_pass1_prefix53

theorem ttFiber8State54_in_pass1_prefix54 :
    ttFiber8StateAt 54 ∈ chainClosureStep ttWord ttFiber8Prefix54 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 49 ∈
      chainClosureStep ttWord ttFiber8Prefix53 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix53 = ttFiber8Prefix49 ++ [ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53]
      (chainClosureStep ttWord ttFiber8Prefix49 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 49) ttFiber8State49_in_pass1_prefix49
  rw [show ttFiber8Prefix54 = ttFiber8Prefix53 ++ [ttFiber8StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 54) []
    (chainClosureStep ttWord ttFiber8Prefix53 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 49) hparentBefore ttFiber8ReverseSingleStep54

theorem ttFiber8State54_in_pass1_full :
    ttFiber8StateAt 54 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix54 ++ [ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix54 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 54) ttFiber8State54_in_pass1_prefix54

theorem ttFiber8State55_in_pass1_prefix55 :
    ttFiber8StateAt 55 ∈ chainClosureStep ttWord ttFiber8Prefix55 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 48 ∈
      chainClosureStep ttWord ttFiber8Prefix54 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix54 = ttFiber8Prefix48 ++ [ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54]
      (chainClosureStep ttWord ttFiber8Prefix48 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 48) ttFiber8State48_in_pass1_prefix48
  rw [show ttFiber8Prefix55 = ttFiber8Prefix54 ++ [ttFiber8StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 55) []
    (chainClosureStep ttWord ttFiber8Prefix54 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 48) hparentBefore ttFiber8ReverseSingleStep55

theorem ttFiber8State55_in_pass1_full :
    ttFiber8StateAt 55 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix55 ++ [ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix55 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 55) ttFiber8State55_in_pass1_prefix55

theorem ttFiber8State56_in_pass1_prefix56 :
    ttFiber8StateAt 56 ∈ chainClosureStep ttWord ttFiber8Prefix56 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 40 ∈
      chainClosureStep ttWord ttFiber8Prefix55 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix55 = ttFiber8Prefix40 ++ [ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55]
      (chainClosureStep ttWord ttFiber8Prefix40 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 40) ttFiber8State40_in_pass1_prefix40
  rw [show ttFiber8Prefix56 = ttFiber8Prefix55 ++ [ttFiber8StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 56) []
    (chainClosureStep ttWord ttFiber8Prefix55 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 40) hparentBefore ttFiber8ReverseSingleStep56

theorem ttFiber8State56_in_pass1_full :
    ttFiber8StateAt 56 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix56 ++ [ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix56 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 56) ttFiber8State56_in_pass1_prefix56

theorem ttFiber8State57_in_pass1_prefix57 :
    ttFiber8StateAt 57 ∈ chainClosureStep ttWord ttFiber8Prefix57 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 41 ∈
      chainClosureStep ttWord ttFiber8Prefix56 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix56 = ttFiber8Prefix41 ++ [ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56]
      (chainClosureStep ttWord ttFiber8Prefix41 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 41) ttFiber8State41_in_pass1_prefix41
  rw [show ttFiber8Prefix57 = ttFiber8Prefix56 ++ [ttFiber8StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 57) []
    (chainClosureStep ttWord ttFiber8Prefix56 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 41) hparentBefore ttFiber8ReverseSingleStep57

theorem ttFiber8State57_in_pass1_full :
    ttFiber8StateAt 57 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix57 ++ [ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix57 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 57) ttFiber8State57_in_pass1_prefix57

theorem ttFiber8State58_in_pass1_prefix58 :
    ttFiber8StateAt 58 ∈ chainClosureStep ttWord ttFiber8Prefix58 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 26 ∈
      chainClosureStep ttWord ttFiber8Prefix57 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix57 = ttFiber8Prefix26 ++ [ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57]
      (chainClosureStep ttWord ttFiber8Prefix26 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 26) ttFiber8State26_in_pass1_prefix26
  rw [show ttFiber8Prefix58 = ttFiber8Prefix57 ++ [ttFiber8StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 58) []
    (chainClosureStep ttWord ttFiber8Prefix57 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 26) hparentBefore ttFiber8ReverseSingleStep58

theorem ttFiber8State58_in_pass1_full :
    ttFiber8StateAt 58 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix58 ++ [ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix58 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 58) ttFiber8State58_in_pass1_prefix58

theorem ttFiber8State59_in_pass1_prefix59 :
    ttFiber8StateAt 59 ∈ chainClosureStep ttWord ttFiber8Prefix59 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 27 ∈
      chainClosureStep ttWord ttFiber8Prefix58 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix58 = ttFiber8Prefix27 ++ [ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58]
      (chainClosureStep ttWord ttFiber8Prefix27 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 27) ttFiber8State27_in_pass1_prefix27
  rw [show ttFiber8Prefix59 = ttFiber8Prefix58 ++ [ttFiber8StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 59) []
    (chainClosureStep ttWord ttFiber8Prefix58 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 27) hparentBefore ttFiber8ReverseSingleStep59

theorem ttFiber8State59_in_pass1_full :
    ttFiber8StateAt 59 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix59 ++ [ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix59 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 59) ttFiber8State59_in_pass1_prefix59

theorem ttFiber8State60_in_pass1_prefix60 :
    ttFiber8StateAt 60 ∈ chainClosureStep ttWord ttFiber8Prefix60 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 28 ∈
      chainClosureStep ttWord ttFiber8Prefix59 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix59 = ttFiber8Prefix28 ++ [ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59]
      (chainClosureStep ttWord ttFiber8Prefix28 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 28) ttFiber8State28_in_pass1_prefix28
  rw [show ttFiber8Prefix60 = ttFiber8Prefix59 ++ [ttFiber8StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 60) []
    (chainClosureStep ttWord ttFiber8Prefix59 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 28) hparentBefore ttFiber8ReverseSingleStep60

theorem ttFiber8State60_in_pass1_full :
    ttFiber8StateAt 60 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix60 ++ [ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix60 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 60) ttFiber8State60_in_pass1_prefix60

theorem ttFiber8State61_in_pass1_prefix61 :
    ttFiber8StateAt 61 ∈ chainClosureStep ttWord ttFiber8Prefix61 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 29 ∈
      chainClosureStep ttWord ttFiber8Prefix60 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix60 = ttFiber8Prefix29 ++ [ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60]
      (chainClosureStep ttWord ttFiber8Prefix29 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 29) ttFiber8State29_in_pass1_prefix29
  rw [show ttFiber8Prefix61 = ttFiber8Prefix60 ++ [ttFiber8StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 61) []
    (chainClosureStep ttWord ttFiber8Prefix60 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 29) hparentBefore ttFiber8ReverseSingleStep61

theorem ttFiber8State61_in_pass1_full :
    ttFiber8StateAt 61 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix61 ++ [ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix61 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 61) ttFiber8State61_in_pass1_prefix61

theorem ttFiber8State62_in_pass1_prefix62 :
    ttFiber8StateAt 62 ∈ chainClosureStep ttWord ttFiber8Prefix62 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 60 ∈
      chainClosureStep ttWord ttFiber8Prefix61 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix61 = ttFiber8Prefix60 ++ [ttFiber8StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 61]
      (chainClosureStep ttWord ttFiber8Prefix60 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 60) ttFiber8State60_in_pass1_prefix60
  rw [show ttFiber8Prefix62 = ttFiber8Prefix61 ++ [ttFiber8StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 62) []
    (chainClosureStep ttWord ttFiber8Prefix61 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 60) hparentBefore ttFiber8ReverseSingleStep62

theorem ttFiber8State62_in_pass1_full :
    ttFiber8StateAt 62 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix62 ++ [ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix62 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 62) ttFiber8State62_in_pass1_prefix62

theorem ttFiber8State63_in_pass1_prefix63 :
    ttFiber8StateAt 63 ∈ chainClosureStep ttWord ttFiber8Prefix63 ([ttFiber8StateAt 0]) := by
  have hparentBefore : ttFiber8StateAt 31 ∈
      chainClosureStep ttWord ttFiber8Prefix62 ([ttFiber8StateAt 0]) := by
    rw [show ttFiber8Prefix62 = ttFiber8Prefix31 ++ [ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62]
      (chainClosureStep ttWord ttFiber8Prefix31 ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 31) ttFiber8State31_in_pass1_prefix31
  rw [show ttFiber8Prefix63 = ttFiber8Prefix62 ++ [ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 63) []
    (chainClosureStep ttWord ttFiber8Prefix62 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 31) hparentBefore ttFiber8ReverseSingleStep63

theorem ttFiber8State63_in_pass1_full :
    ttFiber8StateAt 63 ∈ chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber8Prefix63 ([ttFiber8StateAt 0]))
    (ttFiber8StateAt 63) ttFiber8State63_in_pass1_prefix63

theorem ttFiber8State16_in_pass2_prefix16 :
    ttFiber8StateAt 16 ∈ chainClosureStep ttWord ttFiber8Prefix16 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  have hparentBefore : ttFiber8StateAt 20 ∈
      chainClosureStep ttWord ttFiber8Prefix15 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix15
      (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 20) ttFiber8State20_in_pass1_full
  rw [show ttFiber8Prefix16 = ttFiber8Prefix15 ++ [ttFiber8StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 16) []
    (chainClosureStep ttWord ttFiber8Prefix15 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 20) hparentBefore ttFiber8ReverseSingleStep16

theorem ttFiber8State16_in_pass2_full :
    ttFiber8StateAt 16 ∈ chainClosureStep ttWord ttFiber8DirectStates (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix16 ++ [ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 17, ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix16 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 16) ttFiber8State16_in_pass2_prefix16

theorem ttFiber8State17_in_pass2_prefix17 :
    ttFiber8StateAt 17 ∈ chainClosureStep ttWord ttFiber8Prefix17 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  have hparentBefore : ttFiber8StateAt 21 ∈
      chainClosureStep ttWord ttFiber8Prefix16 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix16
      (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 21) ttFiber8State21_in_pass1_full
  rw [show ttFiber8Prefix17 = ttFiber8Prefix16 ++ [ttFiber8StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 17) []
    (chainClosureStep ttWord ttFiber8Prefix16 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 21) hparentBefore ttFiber8ReverseSingleStep17

theorem ttFiber8State17_in_pass2_full :
    ttFiber8StateAt 17 ∈ chainClosureStep ttWord ttFiber8DirectStates (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix17 ++ [ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 18, ttFiber8StateAt 19, ttFiber8StateAt 20, ttFiber8StateAt 21, ttFiber8StateAt 22, ttFiber8StateAt 23, ttFiber8StateAt 24, ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix17 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 17) ttFiber8State17_in_pass2_prefix17

theorem ttFiber8State24_in_pass2_prefix24 :
    ttFiber8StateAt 24 ∈ chainClosureStep ttWord ttFiber8Prefix24 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  have hparentBefore : ttFiber8StateAt 28 ∈
      chainClosureStep ttWord ttFiber8Prefix23 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix23
      (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 28) ttFiber8State28_in_pass1_full
  rw [show ttFiber8Prefix24 = ttFiber8Prefix23 ++ [ttFiber8StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 24) []
    (chainClosureStep ttWord ttFiber8Prefix23 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 28) hparentBefore ttFiber8ReverseSingleStep24

theorem ttFiber8State24_in_pass2_full :
    ttFiber8StateAt 24 ∈ chainClosureStep ttWord ttFiber8DirectStates (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix24 ++ [ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 25, ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix24 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 24) ttFiber8State24_in_pass2_prefix24

theorem ttFiber8State25_in_pass2_prefix25 :
    ttFiber8StateAt 25 ∈ chainClosureStep ttWord ttFiber8Prefix25 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  have hparentBefore : ttFiber8StateAt 29 ∈
      chainClosureStep ttWord ttFiber8Prefix24 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber8Prefix24
      (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0]))
      (ttFiber8StateAt 29) ttFiber8State29_in_pass1_full
  rw [show ttFiber8Prefix25 = ttFiber8Prefix24 ++ [ttFiber8StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber8StateAt 25) []
    (chainClosureStep ttWord ttFiber8Prefix24 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 29) hparentBefore ttFiber8ReverseSingleStep25

theorem ttFiber8State25_in_pass2_full :
    ttFiber8StateAt 25 ∈ chainClosureStep ttWord ttFiber8DirectStates (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])) := by
  rw [show ttFiber8DirectStates = ttFiber8Prefix25 ++ [ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber8StateAt 26, ttFiber8StateAt 27, ttFiber8StateAt 28, ttFiber8StateAt 29, ttFiber8StateAt 30, ttFiber8StateAt 31, ttFiber8StateAt 32, ttFiber8StateAt 33, ttFiber8StateAt 34, ttFiber8StateAt 35, ttFiber8StateAt 36, ttFiber8StateAt 37, ttFiber8StateAt 38, ttFiber8StateAt 39, ttFiber8StateAt 40, ttFiber8StateAt 41, ttFiber8StateAt 42, ttFiber8StateAt 43, ttFiber8StateAt 44, ttFiber8StateAt 45, ttFiber8StateAt 46, ttFiber8StateAt 47, ttFiber8StateAt 48, ttFiber8StateAt 49, ttFiber8StateAt 50, ttFiber8StateAt 51, ttFiber8StateAt 52, ttFiber8StateAt 53, ttFiber8StateAt 54, ttFiber8StateAt 55, ttFiber8StateAt 56, ttFiber8StateAt 57, ttFiber8StateAt 58, ttFiber8StateAt 59, ttFiber8StateAt 60, ttFiber8StateAt 61, ttFiber8StateAt 62, ttFiber8StateAt 63]
    (chainClosureStep ttWord ttFiber8Prefix25 (chainClosureStep ttWord ttFiber8DirectStates ([ttFiber8StateAt 0])))
    (ttFiber8StateAt 25) ttFiber8State25_in_pass2_prefix25

theorem ttFiber8State0_in_close :
    ttFiber8StateAt 0 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber8DirectStates ttFiber8DirectStates.length
    [ttFiber8StateAt 0] (ttFiber8StateAt 0) (by simp)

theorem ttFiber8State1_in_close :
    ttFiber8StateAt 1 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 1 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 1) ttFiber8State1_in_pass1_full

theorem ttFiber8State2_in_close :
    ttFiber8StateAt 2 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 2 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 2) ttFiber8State2_in_pass1_full

theorem ttFiber8State3_in_close :
    ttFiber8StateAt 3 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 3 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 3) ttFiber8State3_in_pass1_full

theorem ttFiber8State4_in_close :
    ttFiber8StateAt 4 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 4 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 4) ttFiber8State4_in_pass1_full

theorem ttFiber8State5_in_close :
    ttFiber8StateAt 5 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 5 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 5) ttFiber8State5_in_pass1_full

theorem ttFiber8State6_in_close :
    ttFiber8StateAt 6 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 6 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 6) ttFiber8State6_in_pass1_full

theorem ttFiber8State7_in_close :
    ttFiber8StateAt 7 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 7 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 7) ttFiber8State7_in_pass1_full

theorem ttFiber8State8_in_close :
    ttFiber8StateAt 8 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 8 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 8) ttFiber8State8_in_pass1_full

theorem ttFiber8State9_in_close :
    ttFiber8StateAt 9 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 9 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 9) ttFiber8State9_in_pass1_full

theorem ttFiber8State10_in_close :
    ttFiber8StateAt 10 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 10 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 10) ttFiber8State10_in_pass1_full

theorem ttFiber8State11_in_close :
    ttFiber8StateAt 11 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 11 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 11) ttFiber8State11_in_pass1_full

theorem ttFiber8State12_in_close :
    ttFiber8StateAt 12 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 12 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 12) ttFiber8State12_in_pass1_full

theorem ttFiber8State13_in_close :
    ttFiber8StateAt 13 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 13 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 13) ttFiber8State13_in_pass1_full

theorem ttFiber8State14_in_close :
    ttFiber8StateAt 14 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 14 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 14) ttFiber8State14_in_pass1_full

theorem ttFiber8State15_in_close :
    ttFiber8StateAt 15 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 15 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 15) ttFiber8State15_in_pass1_full

theorem ttFiber8State16_in_close :
    ttFiber8StateAt 16 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 16 ∈ closeChainFiber ttWord ttFiber8DirectStates (62 + 2)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber8DirectStates 62
    [ttFiber8StateAt 0] (ttFiber8StateAt 16) ttFiber8FirstPassGrows
    ttFiber8State16_in_pass2_full

theorem ttFiber8State17_in_close :
    ttFiber8StateAt 17 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 17 ∈ closeChainFiber ttWord ttFiber8DirectStates (62 + 2)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber8DirectStates 62
    [ttFiber8StateAt 0] (ttFiber8StateAt 17) ttFiber8FirstPassGrows
    ttFiber8State17_in_pass2_full

theorem ttFiber8State18_in_close :
    ttFiber8StateAt 18 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 18 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 18) ttFiber8State18_in_pass1_full

theorem ttFiber8State19_in_close :
    ttFiber8StateAt 19 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 19 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 19) ttFiber8State19_in_pass1_full

theorem ttFiber8State20_in_close :
    ttFiber8StateAt 20 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 20 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 20) ttFiber8State20_in_pass1_full

theorem ttFiber8State21_in_close :
    ttFiber8StateAt 21 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 21 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 21) ttFiber8State21_in_pass1_full

theorem ttFiber8State22_in_close :
    ttFiber8StateAt 22 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 22 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 22) ttFiber8State22_in_pass1_full

theorem ttFiber8State23_in_close :
    ttFiber8StateAt 23 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 23 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 23) ttFiber8State23_in_pass1_full

theorem ttFiber8State24_in_close :
    ttFiber8StateAt 24 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 24 ∈ closeChainFiber ttWord ttFiber8DirectStates (62 + 2)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber8DirectStates 62
    [ttFiber8StateAt 0] (ttFiber8StateAt 24) ttFiber8FirstPassGrows
    ttFiber8State24_in_pass2_full

theorem ttFiber8State25_in_close :
    ttFiber8StateAt 25 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 25 ∈ closeChainFiber ttWord ttFiber8DirectStates (62 + 2)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber8DirectStates 62
    [ttFiber8StateAt 0] (ttFiber8StateAt 25) ttFiber8FirstPassGrows
    ttFiber8State25_in_pass2_full

theorem ttFiber8State26_in_close :
    ttFiber8StateAt 26 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 26 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 26) ttFiber8State26_in_pass1_full

theorem ttFiber8State27_in_close :
    ttFiber8StateAt 27 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 27 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 27) ttFiber8State27_in_pass1_full

theorem ttFiber8State28_in_close :
    ttFiber8StateAt 28 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 28 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 28) ttFiber8State28_in_pass1_full

theorem ttFiber8State29_in_close :
    ttFiber8StateAt 29 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 29 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 29) ttFiber8State29_in_pass1_full

theorem ttFiber8State30_in_close :
    ttFiber8StateAt 30 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 30 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 30) ttFiber8State30_in_pass1_full

theorem ttFiber8State31_in_close :
    ttFiber8StateAt 31 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 31 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 31) ttFiber8State31_in_pass1_full

theorem ttFiber8State32_in_close :
    ttFiber8StateAt 32 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 32 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 32) ttFiber8State32_in_pass1_full

theorem ttFiber8State33_in_close :
    ttFiber8StateAt 33 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 33 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 33) ttFiber8State33_in_pass1_full

theorem ttFiber8State34_in_close :
    ttFiber8StateAt 34 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 34 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 34) ttFiber8State34_in_pass1_full

theorem ttFiber8State35_in_close :
    ttFiber8StateAt 35 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 35 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 35) ttFiber8State35_in_pass1_full

theorem ttFiber8State36_in_close :
    ttFiber8StateAt 36 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 36 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 36) ttFiber8State36_in_pass1_full

theorem ttFiber8State37_in_close :
    ttFiber8StateAt 37 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 37 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 37) ttFiber8State37_in_pass1_full

theorem ttFiber8State38_in_close :
    ttFiber8StateAt 38 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 38 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 38) ttFiber8State38_in_pass1_full

theorem ttFiber8State39_in_close :
    ttFiber8StateAt 39 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 39 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 39) ttFiber8State39_in_pass1_full

theorem ttFiber8State40_in_close :
    ttFiber8StateAt 40 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 40 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 40) ttFiber8State40_in_pass1_full

theorem ttFiber8State41_in_close :
    ttFiber8StateAt 41 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 41 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 41) ttFiber8State41_in_pass1_full

theorem ttFiber8State42_in_close :
    ttFiber8StateAt 42 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 42 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 42) ttFiber8State42_in_pass1_full

theorem ttFiber8State43_in_close :
    ttFiber8StateAt 43 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 43 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 43) ttFiber8State43_in_pass1_full

theorem ttFiber8State44_in_close :
    ttFiber8StateAt 44 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 44 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 44) ttFiber8State44_in_pass1_full

theorem ttFiber8State45_in_close :
    ttFiber8StateAt 45 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 45 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 45) ttFiber8State45_in_pass1_full

theorem ttFiber8State46_in_close :
    ttFiber8StateAt 46 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 46 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 46) ttFiber8State46_in_pass1_full

theorem ttFiber8State47_in_close :
    ttFiber8StateAt 47 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 47 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 47) ttFiber8State47_in_pass1_full

theorem ttFiber8State48_in_close :
    ttFiber8StateAt 48 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 48 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 48) ttFiber8State48_in_pass1_full

theorem ttFiber8State49_in_close :
    ttFiber8StateAt 49 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 49 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 49) ttFiber8State49_in_pass1_full

theorem ttFiber8State50_in_close :
    ttFiber8StateAt 50 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 50 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 50) ttFiber8State50_in_pass1_full

theorem ttFiber8State51_in_close :
    ttFiber8StateAt 51 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 51 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 51) ttFiber8State51_in_pass1_full

theorem ttFiber8State52_in_close :
    ttFiber8StateAt 52 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 52 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 52) ttFiber8State52_in_pass1_full

theorem ttFiber8State53_in_close :
    ttFiber8StateAt 53 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 53 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 53) ttFiber8State53_in_pass1_full

theorem ttFiber8State54_in_close :
    ttFiber8StateAt 54 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 54 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 54) ttFiber8State54_in_pass1_full

theorem ttFiber8State55_in_close :
    ttFiber8StateAt 55 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 55 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 55) ttFiber8State55_in_pass1_full

theorem ttFiber8State56_in_close :
    ttFiber8StateAt 56 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 56 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 56) ttFiber8State56_in_pass1_full

theorem ttFiber8State57_in_close :
    ttFiber8StateAt 57 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 57 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 57) ttFiber8State57_in_pass1_full

theorem ttFiber8State58_in_close :
    ttFiber8StateAt 58 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 58 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 58) ttFiber8State58_in_pass1_full

theorem ttFiber8State59_in_close :
    ttFiber8StateAt 59 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 59 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 59) ttFiber8State59_in_pass1_full

theorem ttFiber8State60_in_close :
    ttFiber8StateAt 60 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 60 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 60) ttFiber8State60_in_pass1_full

theorem ttFiber8State61_in_close :
    ttFiber8StateAt 61 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 61 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 61) ttFiber8State61_in_pass1_full

theorem ttFiber8State62_in_close :
    ttFiber8StateAt 62 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 62 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 62) ttFiber8State62_in_pass1_full

theorem ttFiber8State63_in_close :
    ttFiber8StateAt 63 ∈
      closeChainFiber ttWord ttFiber8DirectStates ttFiber8DirectStates.length
        [ttFiber8StateAt 0] := by
  change ttFiber8StateAt 63 ∈ closeChainFiber ttWord ttFiber8DirectStates (63 + 1)
    [ttFiber8StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber8DirectStates 63
    [ttFiber8StateAt 0] (ttFiber8StateAt 63) ttFiber8State63_in_pass1_full

theorem ttFiber8DirectConnected :
    chainFiberConnected ttWord ttFiber8DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber8DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber8State0_in_close
  · subst state
    exact ttFiber8State1_in_close
  · subst state
    exact ttFiber8State2_in_close
  · subst state
    exact ttFiber8State3_in_close
  · subst state
    exact ttFiber8State4_in_close
  · subst state
    exact ttFiber8State5_in_close
  · subst state
    exact ttFiber8State6_in_close
  · subst state
    exact ttFiber8State7_in_close
  · subst state
    exact ttFiber8State8_in_close
  · subst state
    exact ttFiber8State9_in_close
  · subst state
    exact ttFiber8State10_in_close
  · subst state
    exact ttFiber8State11_in_close
  · subst state
    exact ttFiber8State12_in_close
  · subst state
    exact ttFiber8State13_in_close
  · subst state
    exact ttFiber8State14_in_close
  · subst state
    exact ttFiber8State15_in_close
  · subst state
    exact ttFiber8State16_in_close
  · subst state
    exact ttFiber8State17_in_close
  · subst state
    exact ttFiber8State18_in_close
  · subst state
    exact ttFiber8State19_in_close
  · subst state
    exact ttFiber8State20_in_close
  · subst state
    exact ttFiber8State21_in_close
  · subst state
    exact ttFiber8State22_in_close
  · subst state
    exact ttFiber8State23_in_close
  · subst state
    exact ttFiber8State24_in_close
  · subst state
    exact ttFiber8State25_in_close
  · subst state
    exact ttFiber8State26_in_close
  · subst state
    exact ttFiber8State27_in_close
  · subst state
    exact ttFiber8State28_in_close
  · subst state
    exact ttFiber8State29_in_close
  · subst state
    exact ttFiber8State30_in_close
  · subst state
    exact ttFiber8State31_in_close
  · subst state
    exact ttFiber8State32_in_close
  · subst state
    exact ttFiber8State33_in_close
  · subst state
    exact ttFiber8State34_in_close
  · subst state
    exact ttFiber8State35_in_close
  · subst state
    exact ttFiber8State36_in_close
  · subst state
    exact ttFiber8State37_in_close
  · subst state
    exact ttFiber8State38_in_close
  · subst state
    exact ttFiber8State39_in_close
  · subst state
    exact ttFiber8State40_in_close
  · subst state
    exact ttFiber8State41_in_close
  · subst state
    exact ttFiber8State42_in_close
  · subst state
    exact ttFiber8State43_in_close
  · subst state
    exact ttFiber8State44_in_close
  · subst state
    exact ttFiber8State45_in_close
  · subst state
    exact ttFiber8State46_in_close
  · subst state
    exact ttFiber8State47_in_close
  · subst state
    exact ttFiber8State48_in_close
  · subst state
    exact ttFiber8State49_in_close
  · subst state
    exact ttFiber8State50_in_close
  · subst state
    exact ttFiber8State51_in_close
  · subst state
    exact ttFiber8State52_in_close
  · subst state
    exact ttFiber8State53_in_close
  · subst state
    exact ttFiber8State54_in_close
  · subst state
    exact ttFiber8State55_in_close
  · subst state
    exact ttFiber8State56_in_close
  · subst state
    exact ttFiber8State57_in_close
  · subst state
    exact ttFiber8State58_in_close
  · subst state
    exact ttFiber8State59_in_close
  · subst state
    exact ttFiber8State60_in_close
  · subst state
    exact ttFiber8State61_in_close
  · subst state
    exact ttFiber8State62_in_close
  · subst state
    exact ttFiber8State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
