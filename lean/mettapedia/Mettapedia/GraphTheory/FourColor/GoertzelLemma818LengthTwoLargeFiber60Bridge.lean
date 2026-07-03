import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber60

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber60StateAt (i : Nat) : List TauState :=
  directStates (ttFiber60RowAt i).sourceLeft (ttFiber60RowAt i).sourceRight

def ttFiber60DirectStates : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]

def ttFiber60Prefix0 : List (List TauState) :=
  [ttFiber60StateAt 0]

def ttFiber60Prefix1 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1]

def ttFiber60Prefix2 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2]

def ttFiber60Prefix3 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3]

def ttFiber60Prefix4 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4]

def ttFiber60Prefix5 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5]

def ttFiber60Prefix6 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6]

def ttFiber60Prefix7 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7]

def ttFiber60Prefix8 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8]

def ttFiber60Prefix9 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9]

def ttFiber60Prefix10 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10]

def ttFiber60Prefix11 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11]

def ttFiber60Prefix12 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12]

def ttFiber60Prefix13 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13]

def ttFiber60Prefix14 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14]

def ttFiber60Prefix15 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15]

def ttFiber60Prefix16 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16]

def ttFiber60Prefix17 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17]

def ttFiber60Prefix18 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18]

def ttFiber60Prefix19 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19]

def ttFiber60Prefix20 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20]

def ttFiber60Prefix21 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21]

def ttFiber60Prefix22 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22]

def ttFiber60Prefix23 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23]

def ttFiber60Prefix24 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24]

def ttFiber60Prefix25 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25]

def ttFiber60Prefix26 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26]

def ttFiber60Prefix27 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27]

def ttFiber60Prefix28 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28]

def ttFiber60Prefix29 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29]

def ttFiber60Prefix30 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30]

def ttFiber60Prefix31 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31]

def ttFiber60Prefix32 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32]

def ttFiber60Prefix33 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33]

def ttFiber60Prefix34 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34]

def ttFiber60Prefix35 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35]

def ttFiber60Prefix36 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36]

def ttFiber60Prefix37 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37]

def ttFiber60Prefix38 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38]

def ttFiber60Prefix39 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39]

def ttFiber60Prefix40 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40]

def ttFiber60Prefix41 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41]

def ttFiber60Prefix42 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42]

def ttFiber60Prefix43 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43]

def ttFiber60Prefix44 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44]

def ttFiber60Prefix45 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45]

def ttFiber60Prefix46 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46]

def ttFiber60Prefix47 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47]

def ttFiber60Prefix48 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48]

def ttFiber60Prefix49 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49]

def ttFiber60Prefix50 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50]

def ttFiber60Prefix51 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51]

def ttFiber60Prefix52 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52]

def ttFiber60Prefix53 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53]

def ttFiber60Prefix54 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54]

def ttFiber60Prefix55 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55]

def ttFiber60Prefix56 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56]

def ttFiber60Prefix57 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57]

def ttFiber60Prefix58 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58]

def ttFiber60Prefix59 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59]

def ttFiber60Prefix60 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60]

def ttFiber60Prefix61 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61]

def ttFiber60Prefix62 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62]

def ttFiber60Prefix63 : List (List TauState) :=
  [ttFiber60StateAt 0, ttFiber60StateAt 1, ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]

theorem ttFiber60ReverseRow_1_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk0] at h
  exact h.2

theorem ttFiber60ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 1)
      (ttFiber60RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 1) (by decide) ttFiber60ReverseRow_1_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_2_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk1] at h
  exact h.1

theorem ttFiber60ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 2)
      (ttFiber60RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 2) (by decide) ttFiber60ReverseRow_2_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_3_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk1] at h
  exact h.2

theorem ttFiber60ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 3)
      (ttFiber60RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 3) (by decide) ttFiber60ReverseRow_3_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_4_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk2] at h
  exact h.1

theorem ttFiber60ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 4)
      (ttFiber60RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 4) (by decide) ttFiber60ReverseRow_4_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_5_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk2] at h
  exact h.2

theorem ttFiber60ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 5)
      (ttFiber60RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 5) (by decide) ttFiber60ReverseRow_5_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_6_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk3] at h
  exact h.1

theorem ttFiber60ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 6)
      (ttFiber60RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 6) (by decide) ttFiber60ReverseRow_6_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_7_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk3] at h
  exact h.2

theorem ttFiber60ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 7)
      (ttFiber60RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 7) (by decide) ttFiber60ReverseRow_7_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_8_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk4] at h
  exact h.1

theorem ttFiber60ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 8)
      (ttFiber60RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 8) (by decide) ttFiber60ReverseRow_8_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_9_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk4] at h
  exact h.2

theorem ttFiber60ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 9)
      (ttFiber60RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 9) (by decide) ttFiber60ReverseRow_9_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_10_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk5] at h
  exact h.1

theorem ttFiber60ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 10)
      (ttFiber60RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 10) (by decide) ttFiber60ReverseRow_10_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_11_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk5] at h
  exact h.2

theorem ttFiber60ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 3) (ttFiber60StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 3) (ttFiber60StateAt 11)
      (ttFiber60RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 11) (by decide) ttFiber60ReverseRow_11_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_12_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk6] at h
  exact h.1

theorem ttFiber60ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 4) (ttFiber60StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 4) (ttFiber60StateAt 12)
      (ttFiber60RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 12) (by decide) ttFiber60ReverseRow_12_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_13_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk6] at h
  exact h.2

theorem ttFiber60ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 5) (ttFiber60StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 5) (ttFiber60StateAt 13)
      (ttFiber60RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 13) (by decide) ttFiber60ReverseRow_13_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_14_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk7] at h
  exact h.1

theorem ttFiber60ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 14)
      (ttFiber60RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 14) (by decide) ttFiber60ReverseRow_14_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_15_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk7] at h
  exact h.2

theorem ttFiber60ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 15)
      (ttFiber60RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 15) (by decide) ttFiber60ReverseRow_15_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_16_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk8] at h
  exact h.1

theorem ttFiber60ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 16)
      (ttFiber60RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 16) (by decide) ttFiber60ReverseRow_16_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_17_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk8] at h
  exact h.2

theorem ttFiber60ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 17)
      (ttFiber60RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 17) (by decide) ttFiber60ReverseRow_17_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_18_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk9] at h
  exact h.1

theorem ttFiber60ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 18)
      (ttFiber60RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 18) (by decide) ttFiber60ReverseRow_18_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_19_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk9] at h
  exact h.2

theorem ttFiber60ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 3) (ttFiber60StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 3) (ttFiber60StateAt 19)
      (ttFiber60RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 19) (by decide) ttFiber60ReverseRow_19_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_20_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk10] at h
  exact h.1

theorem ttFiber60ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 16) (ttFiber60StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 16) (ttFiber60StateAt 20)
      (ttFiber60RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 20) (by decide) ttFiber60ReverseRow_20_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_21_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk10] at h
  exact h.2

theorem ttFiber60ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 17) (ttFiber60StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 17) (ttFiber60StateAt 21)
      (ttFiber60RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 21) (by decide) ttFiber60ReverseRow_21_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_22_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk11] at h
  exact h.1

theorem ttFiber60ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 22)
      (ttFiber60RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 22) (by decide) ttFiber60ReverseRow_22_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_23_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk11] at h
  exact h.2

theorem ttFiber60ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 23)
      (ttFiber60RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 23) (by decide) ttFiber60ReverseRow_23_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_24_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk12] at h
  exact h.1

theorem ttFiber60ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 8) (ttFiber60StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 8) (ttFiber60StateAt 24)
      (ttFiber60RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 24) (by decide) ttFiber60ReverseRow_24_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_25_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk12] at h
  exact h.2

theorem ttFiber60ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 9) (ttFiber60StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 9) (ttFiber60StateAt 25)
      (ttFiber60RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 25) (by decide) ttFiber60ReverseRow_25_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_26_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk13] at h
  exact h.1

theorem ttFiber60ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 10) (ttFiber60StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 10) (ttFiber60StateAt 26)
      (ttFiber60RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 26) (by decide) ttFiber60ReverseRow_26_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_27_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk13] at h
  exact h.2

theorem ttFiber60ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 11) (ttFiber60StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 11) (ttFiber60StateAt 27)
      (ttFiber60RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 27) (by decide) ttFiber60ReverseRow_27_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_28_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk14] at h
  exact h.1

theorem ttFiber60ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 24) (ttFiber60StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 24) (ttFiber60StateAt 28)
      (ttFiber60RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 28) (by decide) ttFiber60ReverseRow_28_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_29_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk14] at h
  exact h.2

theorem ttFiber60ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 25) (ttFiber60StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 25) (ttFiber60StateAt 29)
      (ttFiber60RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 29) (by decide) ttFiber60ReverseRow_29_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_30_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk15] at h
  exact h.1

theorem ttFiber60ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 14) (ttFiber60StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 14) (ttFiber60StateAt 30)
      (ttFiber60RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 30) (by decide) ttFiber60ReverseRow_30_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_31_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk15] at h
  exact h.2

theorem ttFiber60ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 15) (ttFiber60StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 15) (ttFiber60StateAt 31)
      (ttFiber60RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 31) (by decide) ttFiber60ReverseRow_31_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_32_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk16] at h
  exact h.1

theorem ttFiber60ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 0) (ttFiber60StateAt 32)
      (ttFiber60RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 32) (by decide) ttFiber60ReverseRow_32_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_33_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk16] at h
  exact h.2

theorem ttFiber60ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 1) (ttFiber60StateAt 33)
      (ttFiber60RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 33) (by decide) ttFiber60ReverseRow_33_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_34_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk17] at h
  exact h.1

theorem ttFiber60ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 2) (ttFiber60StateAt 34)
      (ttFiber60RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 34) (by decide) ttFiber60ReverseRow_34_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_35_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk17] at h
  exact h.2

theorem ttFiber60ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 35)
      (ttFiber60RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 35) (by decide) ttFiber60ReverseRow_35_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_36_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk18] at h
  exact h.1

theorem ttFiber60ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 36)
      (ttFiber60RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 36) (by decide) ttFiber60ReverseRow_36_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_37_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk18] at h
  exact h.2

theorem ttFiber60ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 33) (ttFiber60StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 33) (ttFiber60StateAt 37)
      (ttFiber60RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 37) (by decide) ttFiber60ReverseRow_37_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_38_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk19] at h
  exact h.1

theorem ttFiber60ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 6) (ttFiber60StateAt 38)
      (ttFiber60RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 38) (by decide) ttFiber60ReverseRow_38_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_39_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk19] at h
  exact h.2

theorem ttFiber60ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 7) (ttFiber60StateAt 39)
      (ttFiber60RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 39) (by decide) ttFiber60ReverseRow_39_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_40_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk20] at h
  exact h.1

theorem ttFiber60ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 8) (ttFiber60StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 8) (ttFiber60StateAt 40)
      (ttFiber60RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 40) (by decide) ttFiber60ReverseRow_40_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_41_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk20] at h
  exact h.2

theorem ttFiber60ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 9) (ttFiber60StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 9) (ttFiber60StateAt 41)
      (ttFiber60RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 41) (by decide) ttFiber60ReverseRow_41_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_42_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk21] at h
  exact h.1

theorem ttFiber60ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 10) (ttFiber60StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 10) (ttFiber60StateAt 42)
      (ttFiber60RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 42) (by decide) ttFiber60ReverseRow_42_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_43_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk21] at h
  exact h.2

theorem ttFiber60ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 43)
      (ttFiber60RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 43) (by decide) ttFiber60ReverseRow_43_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_44_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk22] at h
  exact h.1

theorem ttFiber60ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 44)
      (ttFiber60RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 44) (by decide) ttFiber60ReverseRow_44_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_45_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk22] at h
  exact h.2

theorem ttFiber60ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 41) (ttFiber60StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 41) (ttFiber60StateAt 45)
      (ttFiber60RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 45) (by decide) ttFiber60ReverseRow_45_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_46_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk23] at h
  exact h.1

theorem ttFiber60ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 14) (ttFiber60StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 14) (ttFiber60StateAt 46)
      (ttFiber60RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 46) (by decide) ttFiber60ReverseRow_46_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_47_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk23] at h
  exact h.2

theorem ttFiber60ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 15) (ttFiber60StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 15) (ttFiber60StateAt 47)
      (ttFiber60RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 47) (by decide) ttFiber60ReverseRow_47_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_48_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk24] at h
  exact h.1

theorem ttFiber60ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 16) (ttFiber60StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 16) (ttFiber60StateAt 48)
      (ttFiber60RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 48) (by decide) ttFiber60ReverseRow_48_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_49_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk24] at h
  exact h.2

theorem ttFiber60ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 17) (ttFiber60StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 17) (ttFiber60StateAt 49)
      (ttFiber60RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 49) (by decide) ttFiber60ReverseRow_49_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_50_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk25] at h
  exact h.1

theorem ttFiber60ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 18) (ttFiber60StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 18) (ttFiber60StateAt 50)
      (ttFiber60RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 50) (by decide) ttFiber60ReverseRow_50_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_51_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk25] at h
  exact h.2

theorem ttFiber60ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 19) (ttFiber60StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 19) (ttFiber60StateAt 51)
      (ttFiber60RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 51) (by decide) ttFiber60ReverseRow_51_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_52_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk26] at h
  exact h.1

theorem ttFiber60ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 40) (ttFiber60StateAt 52)
      (ttFiber60RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 52) (by decide) ttFiber60ReverseRow_52_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_53_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk26] at h
  exact h.2

theorem ttFiber60ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 41) (ttFiber60StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 41) (ttFiber60StateAt 53)
      (ttFiber60RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 53) (by decide) ttFiber60ReverseRow_53_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_54_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk27] at h
  exact h.1

theorem ttFiber60ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 22) (ttFiber60StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 22) (ttFiber60StateAt 54)
      (ttFiber60RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 54) (by decide) ttFiber60ReverseRow_54_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_55_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk27] at h
  exact h.2

theorem ttFiber60ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 23) (ttFiber60StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 23) (ttFiber60StateAt 55)
      (ttFiber60RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 55) (by decide) ttFiber60ReverseRow_55_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_56_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk28] at h
  exact h.1

theorem ttFiber60ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 39) (ttFiber60StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 39) (ttFiber60StateAt 56)
      (ttFiber60RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 56) (by decide) ttFiber60ReverseRow_56_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_57_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk28] at h
  exact h.2

theorem ttFiber60ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 38) (ttFiber60StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 38) (ttFiber60StateAt 57)
      (ttFiber60RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 57) (by decide) ttFiber60ReverseRow_57_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_58_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk29] at h
  exact h.1

theorem ttFiber60ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 36) (ttFiber60StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 36) (ttFiber60StateAt 58)
      (ttFiber60RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 58) (by decide) ttFiber60ReverseRow_58_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_59_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk29] at h
  exact h.2

theorem ttFiber60ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 37) (ttFiber60StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 37) (ttFiber60StateAt 59)
      (ttFiber60RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 59) (by decide) ttFiber60ReverseRow_59_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_60_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk30] at h
  exact h.1

theorem ttFiber60ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 32) (ttFiber60StateAt 60)
      (ttFiber60RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 60) (by decide) ttFiber60ReverseRow_60_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_61_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk30] at h
  exact h.2

theorem ttFiber60ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 33) (ttFiber60StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 33) (ttFiber60StateAt 61)
      (ttFiber60RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 61) (by decide) ttFiber60ReverseRow_61_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_62_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk31] at h
  exact h.1

theorem ttFiber60ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 34) (ttFiber60StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 34) (ttFiber60StateAt 62)
      (ttFiber60RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 62) (by decide) ttFiber60ReverseRow_62_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60ReverseRow_63_ok' :
    directRowReverseValid ttFiber60Key ttFiber60Expected (ttFiber60RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber60Chunk31] at h
  exact h.2

theorem ttFiber60ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber60StateAt 35) (ttFiber60StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber60StateAt 35) (ttFiber60StateAt 63)
      (ttFiber60RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber60Key ttFiber60Expected
      (ttFiber60RowAt 63) (by decide) ttFiber60ReverseRow_63_ok'
    simpa [ttFiber60StateAt, ttFiber60RowAt, ttFiber60Rows, listGetD, directRow] using h

theorem ttFiber60FirstPassGrows :
    ((chainClosureStep ttWord ttFiber60DirectStates [ttFiber60StateAt 0]).length ==
      [ttFiber60StateAt 0].length) = false := by
  have hroot : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60DirectStates [ttFiber60StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber60DirectStates [ttFiber60StateAt 0]
      (ttFiber60StateAt 0) (by simp)
  have hnew : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60DirectStates [ttFiber60StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber60DirectStates [ttFiber60StateAt 0]
      (ttFiber60StateAt 0) (ttFiber60StateAt 1) (by decide) (by simp)
      ttFiber60ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber60DirectStates [ttFiber60StateAt 0])
    (ttFiber60StateAt 0) (ttFiber60StateAt 1) hroot hnew (by decide)

theorem ttFiber60State0_in_pass0_full :
    ttFiber60StateAt 0 ∈ [ttFiber60StateAt 0] := by
  simp

theorem ttFiber60State0_in_pass1_full :
    ttFiber60StateAt 0 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber60DirectStates
    ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full

theorem ttFiber60State1_in_pass1_prefix1 :
    ttFiber60StateAt 1 ∈ chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix0 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix0
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix1 = ttFiber60Prefix0 ++ [ttFiber60StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 1) []
    (chainClosureStep ttWord ttFiber60Prefix0 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep1

theorem ttFiber60State1_in_pass1_full :
    ttFiber60StateAt 1 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix1 ++ [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1

theorem ttFiber60State2_in_pass1_prefix2 :
    ttFiber60StateAt 2 ∈ chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix1
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix2 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 2) []
    (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep2

theorem ttFiber60State2_in_pass1_full :
    ttFiber60StateAt 2 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix2 ++ [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 2) ttFiber60State2_in_pass1_prefix2

theorem ttFiber60State3_in_pass1_prefix3 :
    ttFiber60StateAt 3 ∈ chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix2 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2]
      (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1
  rw [show ttFiber60Prefix3 = ttFiber60Prefix2 ++ [ttFiber60StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 3) []
    (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) hparentBefore ttFiber60ReverseSingleStep3

theorem ttFiber60State3_in_pass1_full :
    ttFiber60StateAt 3 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix3 ++ [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 3) ttFiber60State3_in_pass1_prefix3

theorem ttFiber60State4_in_pass1_prefix4 :
    ttFiber60StateAt 4 ∈ chainClosureStep ttWord ttFiber60Prefix4 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 2 ∈
      chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix3 = ttFiber60Prefix2 ++ [ttFiber60StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 3]
      (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 2) ttFiber60State2_in_pass1_prefix2
  rw [show ttFiber60Prefix4 = ttFiber60Prefix3 ++ [ttFiber60StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 4) []
    (chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 2) hparentBefore ttFiber60ReverseSingleStep4

theorem ttFiber60State4_in_pass1_full :
    ttFiber60StateAt 4 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix4 ++ [ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix4 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 4) ttFiber60State4_in_pass1_prefix4

theorem ttFiber60State6_in_pass1_prefix6 :
    ttFiber60StateAt 6 ∈ chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60Prefix5 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix5 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5]
      (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1
  rw [show ttFiber60Prefix6 = ttFiber60Prefix5 ++ [ttFiber60StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 6) []
    (chainClosureStep ttWord ttFiber60Prefix5 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) hparentBefore ttFiber60ReverseSingleStep6

theorem ttFiber60State6_in_pass1_full :
    ttFiber60StateAt 6 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix6 ++ [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 6) ttFiber60State6_in_pass1_prefix6

theorem ttFiber60State7_in_pass1_prefix7 :
    ttFiber60StateAt 7 ∈ chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix6
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix7 = ttFiber60Prefix6 ++ [ttFiber60StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 7) []
    (chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep7

theorem ttFiber60State7_in_pass1_full :
    ttFiber60StateAt 7 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix7 ++ [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 7) ttFiber60State7_in_pass1_prefix7

theorem ttFiber60State8_in_pass1_prefix8 :
    ttFiber60StateAt 8 ∈ chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix7
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix8 = ttFiber60Prefix7 ++ [ttFiber60StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 8) []
    (chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep8

theorem ttFiber60State8_in_pass1_full :
    ttFiber60StateAt 8 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix8 ++ [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 8) ttFiber60State8_in_pass1_prefix8

theorem ttFiber60State9_in_pass1_prefix9 :
    ttFiber60StateAt 9 ∈ chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix8 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8]
      (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1
  rw [show ttFiber60Prefix9 = ttFiber60Prefix8 ++ [ttFiber60StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 9) []
    (chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) hparentBefore ttFiber60ReverseSingleStep9

theorem ttFiber60State9_in_pass1_full :
    ttFiber60StateAt 9 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix9 ++ [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 9) ttFiber60State9_in_pass1_prefix9

theorem ttFiber60State10_in_pass1_prefix10 :
    ttFiber60StateAt 10 ∈ chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 2 ∈
      chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix9 = ttFiber60Prefix2 ++ [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9]
      (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 2) ttFiber60State2_in_pass1_prefix2
  rw [show ttFiber60Prefix10 = ttFiber60Prefix9 ++ [ttFiber60StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 10) []
    (chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 2) hparentBefore ttFiber60ReverseSingleStep10

theorem ttFiber60State10_in_pass1_full :
    ttFiber60StateAt 10 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix10 ++ [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 10) ttFiber60State10_in_pass1_prefix10

theorem ttFiber60State11_in_pass1_prefix11 :
    ttFiber60StateAt 11 ∈ chainClosureStep ttWord ttFiber60Prefix11 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 3 ∈
      chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix10 = ttFiber60Prefix3 ++ [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10]
      (chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 3) ttFiber60State3_in_pass1_prefix3
  rw [show ttFiber60Prefix11 = ttFiber60Prefix10 ++ [ttFiber60StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 11) []
    (chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 3) hparentBefore ttFiber60ReverseSingleStep11

theorem ttFiber60State11_in_pass1_full :
    ttFiber60StateAt 11 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix11 ++ [ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix11 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 11) ttFiber60State11_in_pass1_prefix11

theorem ttFiber60State12_in_pass1_prefix12 :
    ttFiber60StateAt 12 ∈ chainClosureStep ttWord ttFiber60Prefix12 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 4 ∈
      chainClosureStep ttWord ttFiber60Prefix11 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix11 = ttFiber60Prefix4 ++ [ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11]
      (chainClosureStep ttWord ttFiber60Prefix4 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 4) ttFiber60State4_in_pass1_prefix4
  rw [show ttFiber60Prefix12 = ttFiber60Prefix11 ++ [ttFiber60StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 12) []
    (chainClosureStep ttWord ttFiber60Prefix11 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 4) hparentBefore ttFiber60ReverseSingleStep12

theorem ttFiber60State12_in_pass1_full :
    ttFiber60StateAt 12 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix12 ++ [ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix12 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 12) ttFiber60State12_in_pass1_prefix12

theorem ttFiber60State14_in_pass1_prefix14 :
    ttFiber60StateAt 14 ∈ chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 6 ∈
      chainClosureStep ttWord ttFiber60Prefix13 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix13 = ttFiber60Prefix6 ++ [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13]
      (chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 6) ttFiber60State6_in_pass1_prefix6
  rw [show ttFiber60Prefix14 = ttFiber60Prefix13 ++ [ttFiber60StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 14) []
    (chainClosureStep ttWord ttFiber60Prefix13 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 6) hparentBefore ttFiber60ReverseSingleStep14

theorem ttFiber60State14_in_pass1_full :
    ttFiber60StateAt 14 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix14 ++ [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 14) ttFiber60State14_in_pass1_prefix14

theorem ttFiber60State15_in_pass1_prefix15 :
    ttFiber60StateAt 15 ∈ chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 7 ∈
      chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix14 = ttFiber60Prefix7 ++ [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14]
      (chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 7) ttFiber60State7_in_pass1_prefix7
  rw [show ttFiber60Prefix15 = ttFiber60Prefix14 ++ [ttFiber60StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 15) []
    (chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 7) hparentBefore ttFiber60ReverseSingleStep15

theorem ttFiber60State15_in_pass1_full :
    ttFiber60StateAt 15 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix15 ++ [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 15) ttFiber60State15_in_pass1_prefix15

theorem ttFiber60State16_in_pass1_prefix16 :
    ttFiber60StateAt 16 ∈ chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix15
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix16 = ttFiber60Prefix15 ++ [ttFiber60StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 16) []
    (chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep16

theorem ttFiber60State16_in_pass1_full :
    ttFiber60StateAt 16 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix16 ++ [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 16) ttFiber60State16_in_pass1_prefix16

theorem ttFiber60State17_in_pass1_prefix17 :
    ttFiber60StateAt 17 ∈ chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix16 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16]
      (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1
  rw [show ttFiber60Prefix17 = ttFiber60Prefix16 ++ [ttFiber60StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 17) []
    (chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) hparentBefore ttFiber60ReverseSingleStep17

theorem ttFiber60State17_in_pass1_full :
    ttFiber60StateAt 17 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix17 ++ [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 17) ttFiber60State17_in_pass1_prefix17

theorem ttFiber60State18_in_pass1_prefix18 :
    ttFiber60StateAt 18 ∈ chainClosureStep ttWord ttFiber60Prefix18 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 2 ∈
      chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix17 = ttFiber60Prefix2 ++ [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17]
      (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 2) ttFiber60State2_in_pass1_prefix2
  rw [show ttFiber60Prefix18 = ttFiber60Prefix17 ++ [ttFiber60StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 18) []
    (chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 2) hparentBefore ttFiber60ReverseSingleStep18

theorem ttFiber60State18_in_pass1_full :
    ttFiber60StateAt 18 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix18 ++ [ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix18 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 18) ttFiber60State18_in_pass1_prefix18

theorem ttFiber60State19_in_pass1_prefix19 :
    ttFiber60StateAt 19 ∈ chainClosureStep ttWord ttFiber60Prefix19 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 3 ∈
      chainClosureStep ttWord ttFiber60Prefix18 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix18 = ttFiber60Prefix3 ++ [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18]
      (chainClosureStep ttWord ttFiber60Prefix3 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 3) ttFiber60State3_in_pass1_prefix3
  rw [show ttFiber60Prefix19 = ttFiber60Prefix18 ++ [ttFiber60StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 19) []
    (chainClosureStep ttWord ttFiber60Prefix18 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 3) hparentBefore ttFiber60ReverseSingleStep19

theorem ttFiber60State19_in_pass1_full :
    ttFiber60StateAt 19 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix19 ++ [ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix19 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 19) ttFiber60State19_in_pass1_prefix19

theorem ttFiber60State20_in_pass1_prefix20 :
    ttFiber60StateAt 20 ∈ chainClosureStep ttWord ttFiber60Prefix20 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 16 ∈
      chainClosureStep ttWord ttFiber60Prefix19 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix19 = ttFiber60Prefix16 ++ [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19]
      (chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 16) ttFiber60State16_in_pass1_prefix16
  rw [show ttFiber60Prefix20 = ttFiber60Prefix19 ++ [ttFiber60StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 20) []
    (chainClosureStep ttWord ttFiber60Prefix19 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 16) hparentBefore ttFiber60ReverseSingleStep20

theorem ttFiber60State20_in_pass1_full :
    ttFiber60StateAt 20 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix20 ++ [ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix20 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 20) ttFiber60State20_in_pass1_prefix20

theorem ttFiber60State21_in_pass1_prefix21 :
    ttFiber60StateAt 21 ∈ chainClosureStep ttWord ttFiber60Prefix21 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 17 ∈
      chainClosureStep ttWord ttFiber60Prefix20 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix20 = ttFiber60Prefix17 ++ [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20]
      (chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 17) ttFiber60State17_in_pass1_prefix17
  rw [show ttFiber60Prefix21 = ttFiber60Prefix20 ++ [ttFiber60StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 21) []
    (chainClosureStep ttWord ttFiber60Prefix20 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 17) hparentBefore ttFiber60ReverseSingleStep21

theorem ttFiber60State21_in_pass1_full :
    ttFiber60StateAt 21 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix21 ++ [ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix21 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 21) ttFiber60State21_in_pass1_prefix21

theorem ttFiber60State22_in_pass1_prefix22 :
    ttFiber60StateAt 22 ∈ chainClosureStep ttWord ttFiber60Prefix22 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 6 ∈
      chainClosureStep ttWord ttFiber60Prefix21 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix21 = ttFiber60Prefix6 ++ [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21]
      (chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 6) ttFiber60State6_in_pass1_prefix6
  rw [show ttFiber60Prefix22 = ttFiber60Prefix21 ++ [ttFiber60StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 22) []
    (chainClosureStep ttWord ttFiber60Prefix21 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 6) hparentBefore ttFiber60ReverseSingleStep22

theorem ttFiber60State22_in_pass1_full :
    ttFiber60StateAt 22 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix22 ++ [ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix22 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 22) ttFiber60State22_in_pass1_prefix22

theorem ttFiber60State23_in_pass1_prefix23 :
    ttFiber60StateAt 23 ∈ chainClosureStep ttWord ttFiber60Prefix23 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 7 ∈
      chainClosureStep ttWord ttFiber60Prefix22 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix22 = ttFiber60Prefix7 ++ [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22]
      (chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 7) ttFiber60State7_in_pass1_prefix7
  rw [show ttFiber60Prefix23 = ttFiber60Prefix22 ++ [ttFiber60StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 23) []
    (chainClosureStep ttWord ttFiber60Prefix22 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 7) hparentBefore ttFiber60ReverseSingleStep23

theorem ttFiber60State23_in_pass1_full :
    ttFiber60StateAt 23 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix23 ++ [ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix23 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 23) ttFiber60State23_in_pass1_prefix23

theorem ttFiber60State24_in_pass1_prefix24 :
    ttFiber60StateAt 24 ∈ chainClosureStep ttWord ttFiber60Prefix24 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 8 ∈
      chainClosureStep ttWord ttFiber60Prefix23 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix23 = ttFiber60Prefix8 ++ [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23]
      (chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 8) ttFiber60State8_in_pass1_prefix8
  rw [show ttFiber60Prefix24 = ttFiber60Prefix23 ++ [ttFiber60StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 24) []
    (chainClosureStep ttWord ttFiber60Prefix23 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 8) hparentBefore ttFiber60ReverseSingleStep24

theorem ttFiber60State24_in_pass1_full :
    ttFiber60StateAt 24 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix24 ++ [ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix24 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 24) ttFiber60State24_in_pass1_prefix24

theorem ttFiber60State25_in_pass1_prefix25 :
    ttFiber60StateAt 25 ∈ chainClosureStep ttWord ttFiber60Prefix25 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 9 ∈
      chainClosureStep ttWord ttFiber60Prefix24 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix24 = ttFiber60Prefix9 ++ [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24]
      (chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 9) ttFiber60State9_in_pass1_prefix9
  rw [show ttFiber60Prefix25 = ttFiber60Prefix24 ++ [ttFiber60StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 25) []
    (chainClosureStep ttWord ttFiber60Prefix24 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 9) hparentBefore ttFiber60ReverseSingleStep25

theorem ttFiber60State25_in_pass1_full :
    ttFiber60StateAt 25 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix25 ++ [ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix25 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 25) ttFiber60State25_in_pass1_prefix25

theorem ttFiber60State26_in_pass1_prefix26 :
    ttFiber60StateAt 26 ∈ chainClosureStep ttWord ttFiber60Prefix26 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 10 ∈
      chainClosureStep ttWord ttFiber60Prefix25 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix25 = ttFiber60Prefix10 ++ [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25]
      (chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 10) ttFiber60State10_in_pass1_prefix10
  rw [show ttFiber60Prefix26 = ttFiber60Prefix25 ++ [ttFiber60StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 26) []
    (chainClosureStep ttWord ttFiber60Prefix25 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 10) hparentBefore ttFiber60ReverseSingleStep26

theorem ttFiber60State26_in_pass1_full :
    ttFiber60StateAt 26 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix26 ++ [ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix26 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 26) ttFiber60State26_in_pass1_prefix26

theorem ttFiber60State27_in_pass1_prefix27 :
    ttFiber60StateAt 27 ∈ chainClosureStep ttWord ttFiber60Prefix27 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 11 ∈
      chainClosureStep ttWord ttFiber60Prefix26 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix26 = ttFiber60Prefix11 ++ [ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26]
      (chainClosureStep ttWord ttFiber60Prefix11 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 11) ttFiber60State11_in_pass1_prefix11
  rw [show ttFiber60Prefix27 = ttFiber60Prefix26 ++ [ttFiber60StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 27) []
    (chainClosureStep ttWord ttFiber60Prefix26 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 11) hparentBefore ttFiber60ReverseSingleStep27

theorem ttFiber60State27_in_pass1_full :
    ttFiber60StateAt 27 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix27 ++ [ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix27 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 27) ttFiber60State27_in_pass1_prefix27

theorem ttFiber60State28_in_pass1_prefix28 :
    ttFiber60StateAt 28 ∈ chainClosureStep ttWord ttFiber60Prefix28 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 24 ∈
      chainClosureStep ttWord ttFiber60Prefix27 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix27 = ttFiber60Prefix24 ++ [ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27]
      (chainClosureStep ttWord ttFiber60Prefix24 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 24) ttFiber60State24_in_pass1_prefix24
  rw [show ttFiber60Prefix28 = ttFiber60Prefix27 ++ [ttFiber60StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 28) []
    (chainClosureStep ttWord ttFiber60Prefix27 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 24) hparentBefore ttFiber60ReverseSingleStep28

theorem ttFiber60State28_in_pass1_full :
    ttFiber60StateAt 28 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix28 ++ [ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix28 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 28) ttFiber60State28_in_pass1_prefix28

theorem ttFiber60State29_in_pass1_prefix29 :
    ttFiber60StateAt 29 ∈ chainClosureStep ttWord ttFiber60Prefix29 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 25 ∈
      chainClosureStep ttWord ttFiber60Prefix28 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix28 = ttFiber60Prefix25 ++ [ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28]
      (chainClosureStep ttWord ttFiber60Prefix25 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 25) ttFiber60State25_in_pass1_prefix25
  rw [show ttFiber60Prefix29 = ttFiber60Prefix28 ++ [ttFiber60StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 29) []
    (chainClosureStep ttWord ttFiber60Prefix28 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 25) hparentBefore ttFiber60ReverseSingleStep29

theorem ttFiber60State29_in_pass1_full :
    ttFiber60StateAt 29 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix29 ++ [ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix29 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 29) ttFiber60State29_in_pass1_prefix29

theorem ttFiber60State30_in_pass1_prefix30 :
    ttFiber60StateAt 30 ∈ chainClosureStep ttWord ttFiber60Prefix30 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 14 ∈
      chainClosureStep ttWord ttFiber60Prefix29 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix29 = ttFiber60Prefix14 ++ [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29]
      (chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 14) ttFiber60State14_in_pass1_prefix14
  rw [show ttFiber60Prefix30 = ttFiber60Prefix29 ++ [ttFiber60StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 30) []
    (chainClosureStep ttWord ttFiber60Prefix29 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 14) hparentBefore ttFiber60ReverseSingleStep30

theorem ttFiber60State30_in_pass1_full :
    ttFiber60StateAt 30 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix30 ++ [ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix30 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 30) ttFiber60State30_in_pass1_prefix30

theorem ttFiber60State31_in_pass1_prefix31 :
    ttFiber60StateAt 31 ∈ chainClosureStep ttWord ttFiber60Prefix31 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 15 ∈
      chainClosureStep ttWord ttFiber60Prefix30 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix30 = ttFiber60Prefix15 ++ [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30]
      (chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 15) ttFiber60State15_in_pass1_prefix15
  rw [show ttFiber60Prefix31 = ttFiber60Prefix30 ++ [ttFiber60StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 31) []
    (chainClosureStep ttWord ttFiber60Prefix30 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 15) hparentBefore ttFiber60ReverseSingleStep31

theorem ttFiber60State31_in_pass1_full :
    ttFiber60StateAt 31 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix31 ++ [ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix31 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 31) ttFiber60State31_in_pass1_prefix31

theorem ttFiber60State32_in_pass1_prefix32 :
    ttFiber60StateAt 32 ∈ chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 0 ∈
      chainClosureStep ttWord ttFiber60Prefix31 ([ttFiber60StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix31
      ([ttFiber60StateAt 0]) (ttFiber60StateAt 0) ttFiber60State0_in_pass0_full
  rw [show ttFiber60Prefix32 = ttFiber60Prefix31 ++ [ttFiber60StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 32) []
    (chainClosureStep ttWord ttFiber60Prefix31 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 0) hparentBefore ttFiber60ReverseSingleStep32

theorem ttFiber60State32_in_pass1_full :
    ttFiber60StateAt 32 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix32 ++ [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 32) ttFiber60State32_in_pass1_prefix32

theorem ttFiber60State33_in_pass1_prefix33 :
    ttFiber60StateAt 33 ∈ chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 1 ∈
      chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix32 = ttFiber60Prefix1 ++ [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 2, ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32]
      (chainClosureStep ttWord ttFiber60Prefix1 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 1) ttFiber60State1_in_pass1_prefix1
  rw [show ttFiber60Prefix33 = ttFiber60Prefix32 ++ [ttFiber60StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 33) []
    (chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 1) hparentBefore ttFiber60ReverseSingleStep33

theorem ttFiber60State33_in_pass1_full :
    ttFiber60StateAt 33 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix33 ++ [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 33) ttFiber60State33_in_pass1_prefix33

theorem ttFiber60State34_in_pass1_prefix34 :
    ttFiber60StateAt 34 ∈ chainClosureStep ttWord ttFiber60Prefix34 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 2 ∈
      chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix33 = ttFiber60Prefix2 ++ [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 3, ttFiber60StateAt 4, ttFiber60StateAt 5, ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33]
      (chainClosureStep ttWord ttFiber60Prefix2 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 2) ttFiber60State2_in_pass1_prefix2
  rw [show ttFiber60Prefix34 = ttFiber60Prefix33 ++ [ttFiber60StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 34) []
    (chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 2) hparentBefore ttFiber60ReverseSingleStep34

theorem ttFiber60State34_in_pass1_full :
    ttFiber60StateAt 34 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix34 ++ [ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix34 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 34) ttFiber60State34_in_pass1_prefix34

theorem ttFiber60State35_in_pass1_prefix35 :
    ttFiber60StateAt 35 ∈ chainClosureStep ttWord ttFiber60Prefix35 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 32 ∈
      chainClosureStep ttWord ttFiber60Prefix34 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix34 = ttFiber60Prefix32 ++ [ttFiber60StateAt 33, ttFiber60StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 33, ttFiber60StateAt 34]
      (chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 32) ttFiber60State32_in_pass1_prefix32
  rw [show ttFiber60Prefix35 = ttFiber60Prefix34 ++ [ttFiber60StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 35) []
    (chainClosureStep ttWord ttFiber60Prefix34 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 32) hparentBefore ttFiber60ReverseSingleStep35

theorem ttFiber60State35_in_pass1_full :
    ttFiber60StateAt 35 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix35 ++ [ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix35 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 35) ttFiber60State35_in_pass1_prefix35

theorem ttFiber60State36_in_pass1_prefix36 :
    ttFiber60StateAt 36 ∈ chainClosureStep ttWord ttFiber60Prefix36 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 32 ∈
      chainClosureStep ttWord ttFiber60Prefix35 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix35 = ttFiber60Prefix32 ++ [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35]
      (chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 32) ttFiber60State32_in_pass1_prefix32
  rw [show ttFiber60Prefix36 = ttFiber60Prefix35 ++ [ttFiber60StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 36) []
    (chainClosureStep ttWord ttFiber60Prefix35 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 32) hparentBefore ttFiber60ReverseSingleStep36

theorem ttFiber60State36_in_pass1_full :
    ttFiber60StateAt 36 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix36 ++ [ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix36 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 36) ttFiber60State36_in_pass1_prefix36

theorem ttFiber60State37_in_pass1_prefix37 :
    ttFiber60StateAt 37 ∈ chainClosureStep ttWord ttFiber60Prefix37 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 33 ∈
      chainClosureStep ttWord ttFiber60Prefix36 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix36 = ttFiber60Prefix33 ++ [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36]
      (chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 33) ttFiber60State33_in_pass1_prefix33
  rw [show ttFiber60Prefix37 = ttFiber60Prefix36 ++ [ttFiber60StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 37) []
    (chainClosureStep ttWord ttFiber60Prefix36 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 33) hparentBefore ttFiber60ReverseSingleStep37

theorem ttFiber60State37_in_pass1_full :
    ttFiber60StateAt 37 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix37 ++ [ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix37 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 37) ttFiber60State37_in_pass1_prefix37

theorem ttFiber60State38_in_pass1_prefix38 :
    ttFiber60StateAt 38 ∈ chainClosureStep ttWord ttFiber60Prefix38 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 6 ∈
      chainClosureStep ttWord ttFiber60Prefix37 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix37 = ttFiber60Prefix6 ++ [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37]
      (chainClosureStep ttWord ttFiber60Prefix6 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 6) ttFiber60State6_in_pass1_prefix6
  rw [show ttFiber60Prefix38 = ttFiber60Prefix37 ++ [ttFiber60StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 38) []
    (chainClosureStep ttWord ttFiber60Prefix37 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 6) hparentBefore ttFiber60ReverseSingleStep38

theorem ttFiber60State38_in_pass1_full :
    ttFiber60StateAt 38 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix38 ++ [ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix38 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 38) ttFiber60State38_in_pass1_prefix38

theorem ttFiber60State39_in_pass1_prefix39 :
    ttFiber60StateAt 39 ∈ chainClosureStep ttWord ttFiber60Prefix39 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 7 ∈
      chainClosureStep ttWord ttFiber60Prefix38 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix38 = ttFiber60Prefix7 ++ [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38]
      (chainClosureStep ttWord ttFiber60Prefix7 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 7) ttFiber60State7_in_pass1_prefix7
  rw [show ttFiber60Prefix39 = ttFiber60Prefix38 ++ [ttFiber60StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 39) []
    (chainClosureStep ttWord ttFiber60Prefix38 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 7) hparentBefore ttFiber60ReverseSingleStep39

theorem ttFiber60State39_in_pass1_full :
    ttFiber60StateAt 39 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix39 ++ [ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix39 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 39) ttFiber60State39_in_pass1_prefix39

theorem ttFiber60State40_in_pass1_prefix40 :
    ttFiber60StateAt 40 ∈ chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 8 ∈
      chainClosureStep ttWord ttFiber60Prefix39 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix39 = ttFiber60Prefix8 ++ [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39]
      (chainClosureStep ttWord ttFiber60Prefix8 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 8) ttFiber60State8_in_pass1_prefix8
  rw [show ttFiber60Prefix40 = ttFiber60Prefix39 ++ [ttFiber60StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 40) []
    (chainClosureStep ttWord ttFiber60Prefix39 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 8) hparentBefore ttFiber60ReverseSingleStep40

theorem ttFiber60State40_in_pass1_full :
    ttFiber60StateAt 40 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix40 ++ [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 40) ttFiber60State40_in_pass1_prefix40

theorem ttFiber60State41_in_pass1_prefix41 :
    ttFiber60StateAt 41 ∈ chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 9 ∈
      chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix40 = ttFiber60Prefix9 ++ [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40]
      (chainClosureStep ttWord ttFiber60Prefix9 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 9) ttFiber60State9_in_pass1_prefix9
  rw [show ttFiber60Prefix41 = ttFiber60Prefix40 ++ [ttFiber60StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 41) []
    (chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 9) hparentBefore ttFiber60ReverseSingleStep41

theorem ttFiber60State41_in_pass1_full :
    ttFiber60StateAt 41 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix41 ++ [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 41) ttFiber60State41_in_pass1_prefix41

theorem ttFiber60State42_in_pass1_prefix42 :
    ttFiber60StateAt 42 ∈ chainClosureStep ttWord ttFiber60Prefix42 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 10 ∈
      chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix41 = ttFiber60Prefix10 ++ [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41]
      (chainClosureStep ttWord ttFiber60Prefix10 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 10) ttFiber60State10_in_pass1_prefix10
  rw [show ttFiber60Prefix42 = ttFiber60Prefix41 ++ [ttFiber60StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 42) []
    (chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 10) hparentBefore ttFiber60ReverseSingleStep42

theorem ttFiber60State42_in_pass1_full :
    ttFiber60StateAt 42 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix42 ++ [ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix42 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 42) ttFiber60State42_in_pass1_prefix42

theorem ttFiber60State43_in_pass1_prefix43 :
    ttFiber60StateAt 43 ∈ chainClosureStep ttWord ttFiber60Prefix43 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 40 ∈
      chainClosureStep ttWord ttFiber60Prefix42 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix42 = ttFiber60Prefix40 ++ [ttFiber60StateAt 41, ttFiber60StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 41, ttFiber60StateAt 42]
      (chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 40) ttFiber60State40_in_pass1_prefix40
  rw [show ttFiber60Prefix43 = ttFiber60Prefix42 ++ [ttFiber60StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 43) []
    (chainClosureStep ttWord ttFiber60Prefix42 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 40) hparentBefore ttFiber60ReverseSingleStep43

theorem ttFiber60State43_in_pass1_full :
    ttFiber60StateAt 43 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix43 ++ [ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix43 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 43) ttFiber60State43_in_pass1_prefix43

theorem ttFiber60State44_in_pass1_prefix44 :
    ttFiber60StateAt 44 ∈ chainClosureStep ttWord ttFiber60Prefix44 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 40 ∈
      chainClosureStep ttWord ttFiber60Prefix43 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix43 = ttFiber60Prefix40 ++ [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43]
      (chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 40) ttFiber60State40_in_pass1_prefix40
  rw [show ttFiber60Prefix44 = ttFiber60Prefix43 ++ [ttFiber60StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 44) []
    (chainClosureStep ttWord ttFiber60Prefix43 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 40) hparentBefore ttFiber60ReverseSingleStep44

theorem ttFiber60State44_in_pass1_full :
    ttFiber60StateAt 44 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix44 ++ [ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix44 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 44) ttFiber60State44_in_pass1_prefix44

theorem ttFiber60State45_in_pass1_prefix45 :
    ttFiber60StateAt 45 ∈ chainClosureStep ttWord ttFiber60Prefix45 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 41 ∈
      chainClosureStep ttWord ttFiber60Prefix44 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix44 = ttFiber60Prefix41 ++ [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44]
      (chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 41) ttFiber60State41_in_pass1_prefix41
  rw [show ttFiber60Prefix45 = ttFiber60Prefix44 ++ [ttFiber60StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 45) []
    (chainClosureStep ttWord ttFiber60Prefix44 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 41) hparentBefore ttFiber60ReverseSingleStep45

theorem ttFiber60State45_in_pass1_full :
    ttFiber60StateAt 45 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix45 ++ [ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix45 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 45) ttFiber60State45_in_pass1_prefix45

theorem ttFiber60State46_in_pass1_prefix46 :
    ttFiber60StateAt 46 ∈ chainClosureStep ttWord ttFiber60Prefix46 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 14 ∈
      chainClosureStep ttWord ttFiber60Prefix45 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix45 = ttFiber60Prefix14 ++ [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45]
      (chainClosureStep ttWord ttFiber60Prefix14 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 14) ttFiber60State14_in_pass1_prefix14
  rw [show ttFiber60Prefix46 = ttFiber60Prefix45 ++ [ttFiber60StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 46) []
    (chainClosureStep ttWord ttFiber60Prefix45 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 14) hparentBefore ttFiber60ReverseSingleStep46

theorem ttFiber60State46_in_pass1_full :
    ttFiber60StateAt 46 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix46 ++ [ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix46 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 46) ttFiber60State46_in_pass1_prefix46

theorem ttFiber60State47_in_pass1_prefix47 :
    ttFiber60StateAt 47 ∈ chainClosureStep ttWord ttFiber60Prefix47 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 15 ∈
      chainClosureStep ttWord ttFiber60Prefix46 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix46 = ttFiber60Prefix15 ++ [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46]
      (chainClosureStep ttWord ttFiber60Prefix15 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 15) ttFiber60State15_in_pass1_prefix15
  rw [show ttFiber60Prefix47 = ttFiber60Prefix46 ++ [ttFiber60StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 47) []
    (chainClosureStep ttWord ttFiber60Prefix46 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 15) hparentBefore ttFiber60ReverseSingleStep47

theorem ttFiber60State47_in_pass1_full :
    ttFiber60StateAt 47 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix47 ++ [ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix47 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 47) ttFiber60State47_in_pass1_prefix47

theorem ttFiber60State48_in_pass1_prefix48 :
    ttFiber60StateAt 48 ∈ chainClosureStep ttWord ttFiber60Prefix48 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 16 ∈
      chainClosureStep ttWord ttFiber60Prefix47 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix47 = ttFiber60Prefix16 ++ [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47]
      (chainClosureStep ttWord ttFiber60Prefix16 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 16) ttFiber60State16_in_pass1_prefix16
  rw [show ttFiber60Prefix48 = ttFiber60Prefix47 ++ [ttFiber60StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 48) []
    (chainClosureStep ttWord ttFiber60Prefix47 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 16) hparentBefore ttFiber60ReverseSingleStep48

theorem ttFiber60State48_in_pass1_full :
    ttFiber60StateAt 48 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix48 ++ [ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix48 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 48) ttFiber60State48_in_pass1_prefix48

theorem ttFiber60State49_in_pass1_prefix49 :
    ttFiber60StateAt 49 ∈ chainClosureStep ttWord ttFiber60Prefix49 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 17 ∈
      chainClosureStep ttWord ttFiber60Prefix48 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix48 = ttFiber60Prefix17 ++ [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48]
      (chainClosureStep ttWord ttFiber60Prefix17 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 17) ttFiber60State17_in_pass1_prefix17
  rw [show ttFiber60Prefix49 = ttFiber60Prefix48 ++ [ttFiber60StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 49) []
    (chainClosureStep ttWord ttFiber60Prefix48 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 17) hparentBefore ttFiber60ReverseSingleStep49

theorem ttFiber60State49_in_pass1_full :
    ttFiber60StateAt 49 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix49 ++ [ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix49 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 49) ttFiber60State49_in_pass1_prefix49

theorem ttFiber60State50_in_pass1_prefix50 :
    ttFiber60StateAt 50 ∈ chainClosureStep ttWord ttFiber60Prefix50 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 18 ∈
      chainClosureStep ttWord ttFiber60Prefix49 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix49 = ttFiber60Prefix18 ++ [ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49]
      (chainClosureStep ttWord ttFiber60Prefix18 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 18) ttFiber60State18_in_pass1_prefix18
  rw [show ttFiber60Prefix50 = ttFiber60Prefix49 ++ [ttFiber60StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 50) []
    (chainClosureStep ttWord ttFiber60Prefix49 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 18) hparentBefore ttFiber60ReverseSingleStep50

theorem ttFiber60State50_in_pass1_full :
    ttFiber60StateAt 50 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix50 ++ [ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix50 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 50) ttFiber60State50_in_pass1_prefix50

theorem ttFiber60State51_in_pass1_prefix51 :
    ttFiber60StateAt 51 ∈ chainClosureStep ttWord ttFiber60Prefix51 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 19 ∈
      chainClosureStep ttWord ttFiber60Prefix50 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix50 = ttFiber60Prefix19 ++ [ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50]
      (chainClosureStep ttWord ttFiber60Prefix19 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 19) ttFiber60State19_in_pass1_prefix19
  rw [show ttFiber60Prefix51 = ttFiber60Prefix50 ++ [ttFiber60StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 51) []
    (chainClosureStep ttWord ttFiber60Prefix50 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 19) hparentBefore ttFiber60ReverseSingleStep51

theorem ttFiber60State51_in_pass1_full :
    ttFiber60StateAt 51 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix51 ++ [ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix51 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 51) ttFiber60State51_in_pass1_prefix51

theorem ttFiber60State52_in_pass1_prefix52 :
    ttFiber60StateAt 52 ∈ chainClosureStep ttWord ttFiber60Prefix52 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 40 ∈
      chainClosureStep ttWord ttFiber60Prefix51 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix51 = ttFiber60Prefix40 ++ [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51]
      (chainClosureStep ttWord ttFiber60Prefix40 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 40) ttFiber60State40_in_pass1_prefix40
  rw [show ttFiber60Prefix52 = ttFiber60Prefix51 ++ [ttFiber60StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 52) []
    (chainClosureStep ttWord ttFiber60Prefix51 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 40) hparentBefore ttFiber60ReverseSingleStep52

theorem ttFiber60State52_in_pass1_full :
    ttFiber60StateAt 52 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix52 ++ [ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix52 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 52) ttFiber60State52_in_pass1_prefix52

theorem ttFiber60State53_in_pass1_prefix53 :
    ttFiber60StateAt 53 ∈ chainClosureStep ttWord ttFiber60Prefix53 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 41 ∈
      chainClosureStep ttWord ttFiber60Prefix52 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix52 = ttFiber60Prefix41 ++ [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52]
      (chainClosureStep ttWord ttFiber60Prefix41 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 41) ttFiber60State41_in_pass1_prefix41
  rw [show ttFiber60Prefix53 = ttFiber60Prefix52 ++ [ttFiber60StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 53) []
    (chainClosureStep ttWord ttFiber60Prefix52 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 41) hparentBefore ttFiber60ReverseSingleStep53

theorem ttFiber60State53_in_pass1_full :
    ttFiber60StateAt 53 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix53 ++ [ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix53 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 53) ttFiber60State53_in_pass1_prefix53

theorem ttFiber60State54_in_pass1_prefix54 :
    ttFiber60StateAt 54 ∈ chainClosureStep ttWord ttFiber60Prefix54 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 22 ∈
      chainClosureStep ttWord ttFiber60Prefix53 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix53 = ttFiber60Prefix22 ++ [ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53]
      (chainClosureStep ttWord ttFiber60Prefix22 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 22) ttFiber60State22_in_pass1_prefix22
  rw [show ttFiber60Prefix54 = ttFiber60Prefix53 ++ [ttFiber60StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 54) []
    (chainClosureStep ttWord ttFiber60Prefix53 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 22) hparentBefore ttFiber60ReverseSingleStep54

theorem ttFiber60State54_in_pass1_full :
    ttFiber60StateAt 54 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix54 ++ [ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix54 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 54) ttFiber60State54_in_pass1_prefix54

theorem ttFiber60State55_in_pass1_prefix55 :
    ttFiber60StateAt 55 ∈ chainClosureStep ttWord ttFiber60Prefix55 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 23 ∈
      chainClosureStep ttWord ttFiber60Prefix54 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix54 = ttFiber60Prefix23 ++ [ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54]
      (chainClosureStep ttWord ttFiber60Prefix23 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 23) ttFiber60State23_in_pass1_prefix23
  rw [show ttFiber60Prefix55 = ttFiber60Prefix54 ++ [ttFiber60StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 55) []
    (chainClosureStep ttWord ttFiber60Prefix54 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 23) hparentBefore ttFiber60ReverseSingleStep55

theorem ttFiber60State55_in_pass1_full :
    ttFiber60StateAt 55 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix55 ++ [ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix55 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 55) ttFiber60State55_in_pass1_prefix55

theorem ttFiber60State56_in_pass1_prefix56 :
    ttFiber60StateAt 56 ∈ chainClosureStep ttWord ttFiber60Prefix56 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 39 ∈
      chainClosureStep ttWord ttFiber60Prefix55 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix55 = ttFiber60Prefix39 ++ [ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55]
      (chainClosureStep ttWord ttFiber60Prefix39 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 39) ttFiber60State39_in_pass1_prefix39
  rw [show ttFiber60Prefix56 = ttFiber60Prefix55 ++ [ttFiber60StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 56) []
    (chainClosureStep ttWord ttFiber60Prefix55 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 39) hparentBefore ttFiber60ReverseSingleStep56

theorem ttFiber60State56_in_pass1_full :
    ttFiber60StateAt 56 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix56 ++ [ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix56 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 56) ttFiber60State56_in_pass1_prefix56

theorem ttFiber60State57_in_pass1_prefix57 :
    ttFiber60StateAt 57 ∈ chainClosureStep ttWord ttFiber60Prefix57 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 38 ∈
      chainClosureStep ttWord ttFiber60Prefix56 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix56 = ttFiber60Prefix38 ++ [ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56]
      (chainClosureStep ttWord ttFiber60Prefix38 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 38) ttFiber60State38_in_pass1_prefix38
  rw [show ttFiber60Prefix57 = ttFiber60Prefix56 ++ [ttFiber60StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 57) []
    (chainClosureStep ttWord ttFiber60Prefix56 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 38) hparentBefore ttFiber60ReverseSingleStep57

theorem ttFiber60State57_in_pass1_full :
    ttFiber60StateAt 57 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix57 ++ [ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix57 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 57) ttFiber60State57_in_pass1_prefix57

theorem ttFiber60State58_in_pass1_prefix58 :
    ttFiber60StateAt 58 ∈ chainClosureStep ttWord ttFiber60Prefix58 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 36 ∈
      chainClosureStep ttWord ttFiber60Prefix57 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix57 = ttFiber60Prefix36 ++ [ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57]
      (chainClosureStep ttWord ttFiber60Prefix36 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 36) ttFiber60State36_in_pass1_prefix36
  rw [show ttFiber60Prefix58 = ttFiber60Prefix57 ++ [ttFiber60StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 58) []
    (chainClosureStep ttWord ttFiber60Prefix57 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 36) hparentBefore ttFiber60ReverseSingleStep58

theorem ttFiber60State58_in_pass1_full :
    ttFiber60StateAt 58 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix58 ++ [ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix58 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 58) ttFiber60State58_in_pass1_prefix58

theorem ttFiber60State59_in_pass1_prefix59 :
    ttFiber60StateAt 59 ∈ chainClosureStep ttWord ttFiber60Prefix59 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 37 ∈
      chainClosureStep ttWord ttFiber60Prefix58 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix58 = ttFiber60Prefix37 ++ [ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58]
      (chainClosureStep ttWord ttFiber60Prefix37 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 37) ttFiber60State37_in_pass1_prefix37
  rw [show ttFiber60Prefix59 = ttFiber60Prefix58 ++ [ttFiber60StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 59) []
    (chainClosureStep ttWord ttFiber60Prefix58 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 37) hparentBefore ttFiber60ReverseSingleStep59

theorem ttFiber60State59_in_pass1_full :
    ttFiber60StateAt 59 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix59 ++ [ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix59 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 59) ttFiber60State59_in_pass1_prefix59

theorem ttFiber60State60_in_pass1_prefix60 :
    ttFiber60StateAt 60 ∈ chainClosureStep ttWord ttFiber60Prefix60 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 32 ∈
      chainClosureStep ttWord ttFiber60Prefix59 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix59 = ttFiber60Prefix32 ++ [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59]
      (chainClosureStep ttWord ttFiber60Prefix32 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 32) ttFiber60State32_in_pass1_prefix32
  rw [show ttFiber60Prefix60 = ttFiber60Prefix59 ++ [ttFiber60StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 60) []
    (chainClosureStep ttWord ttFiber60Prefix59 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 32) hparentBefore ttFiber60ReverseSingleStep60

theorem ttFiber60State60_in_pass1_full :
    ttFiber60StateAt 60 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix60 ++ [ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix60 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 60) ttFiber60State60_in_pass1_prefix60

theorem ttFiber60State61_in_pass1_prefix61 :
    ttFiber60StateAt 61 ∈ chainClosureStep ttWord ttFiber60Prefix61 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 33 ∈
      chainClosureStep ttWord ttFiber60Prefix60 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix60 = ttFiber60Prefix33 ++ [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60]
      (chainClosureStep ttWord ttFiber60Prefix33 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 33) ttFiber60State33_in_pass1_prefix33
  rw [show ttFiber60Prefix61 = ttFiber60Prefix60 ++ [ttFiber60StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 61) []
    (chainClosureStep ttWord ttFiber60Prefix60 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 33) hparentBefore ttFiber60ReverseSingleStep61

theorem ttFiber60State61_in_pass1_full :
    ttFiber60StateAt 61 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix61 ++ [ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix61 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 61) ttFiber60State61_in_pass1_prefix61

theorem ttFiber60State62_in_pass1_prefix62 :
    ttFiber60StateAt 62 ∈ chainClosureStep ttWord ttFiber60Prefix62 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 34 ∈
      chainClosureStep ttWord ttFiber60Prefix61 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix61 = ttFiber60Prefix34 ++ [ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61]
      (chainClosureStep ttWord ttFiber60Prefix34 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 34) ttFiber60State34_in_pass1_prefix34
  rw [show ttFiber60Prefix62 = ttFiber60Prefix61 ++ [ttFiber60StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 62) []
    (chainClosureStep ttWord ttFiber60Prefix61 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 34) hparentBefore ttFiber60ReverseSingleStep62

theorem ttFiber60State62_in_pass1_full :
    ttFiber60StateAt 62 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix62 ++ [ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix62 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 62) ttFiber60State62_in_pass1_prefix62

theorem ttFiber60State63_in_pass1_prefix63 :
    ttFiber60StateAt 63 ∈ chainClosureStep ttWord ttFiber60Prefix63 ([ttFiber60StateAt 0]) := by
  have hparentBefore : ttFiber60StateAt 35 ∈
      chainClosureStep ttWord ttFiber60Prefix62 ([ttFiber60StateAt 0]) := by
    rw [show ttFiber60Prefix62 = ttFiber60Prefix35 ++ [ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62]
      (chainClosureStep ttWord ttFiber60Prefix35 ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 35) ttFiber60State35_in_pass1_prefix35
  rw [show ttFiber60Prefix63 = ttFiber60Prefix62 ++ [ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 63) []
    (chainClosureStep ttWord ttFiber60Prefix62 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 35) hparentBefore ttFiber60ReverseSingleStep63

theorem ttFiber60State63_in_pass1_full :
    ttFiber60StateAt 63 ∈ chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber60Prefix63 ([ttFiber60StateAt 0]))
    (ttFiber60StateAt 63) ttFiber60State63_in_pass1_prefix63

theorem ttFiber60State5_in_pass2_prefix5 :
    ttFiber60StateAt 5 ∈ chainClosureStep ttWord ttFiber60Prefix5 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
  have hparentBefore : ttFiber60StateAt 7 ∈
      chainClosureStep ttWord ttFiber60Prefix4 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber60Prefix4
      (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0]))
      (ttFiber60StateAt 7) ttFiber60State7_in_pass1_full
  rw [show ttFiber60Prefix5 = ttFiber60Prefix4 ++ [ttFiber60StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 5) []
    (chainClosureStep ttWord ttFiber60Prefix4 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])))
    (ttFiber60StateAt 7) hparentBefore ttFiber60ReverseSingleStep5

theorem ttFiber60State5_in_pass2_full :
    ttFiber60StateAt 5 ∈ chainClosureStep ttWord ttFiber60DirectStates (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix5 ++ [ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12, ttFiber60StateAt 13, ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix5 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])))
    (ttFiber60StateAt 5) ttFiber60State5_in_pass2_prefix5

theorem ttFiber60State13_in_pass2_prefix13 :
    ttFiber60StateAt 13 ∈ chainClosureStep ttWord ttFiber60Prefix13 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
  have hparentBefore : ttFiber60StateAt 5 ∈
      chainClosureStep ttWord ttFiber60Prefix12 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
    rw [show ttFiber60Prefix12 = ttFiber60Prefix5 ++ [ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 6, ttFiber60StateAt 7, ttFiber60StateAt 8, ttFiber60StateAt 9, ttFiber60StateAt 10, ttFiber60StateAt 11, ttFiber60StateAt 12]
      (chainClosureStep ttWord ttFiber60Prefix5 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])))
      (ttFiber60StateAt 5) ttFiber60State5_in_pass2_prefix5
  rw [show ttFiber60Prefix13 = ttFiber60Prefix12 ++ [ttFiber60StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber60StateAt 13) []
    (chainClosureStep ttWord ttFiber60Prefix12 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])))
    (ttFiber60StateAt 5) hparentBefore ttFiber60ReverseSingleStep13

theorem ttFiber60State13_in_pass2_full :
    ttFiber60StateAt 13 ∈ chainClosureStep ttWord ttFiber60DirectStates (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])) := by
  rw [show ttFiber60DirectStates = ttFiber60Prefix13 ++ [ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber60StateAt 14, ttFiber60StateAt 15, ttFiber60StateAt 16, ttFiber60StateAt 17, ttFiber60StateAt 18, ttFiber60StateAt 19, ttFiber60StateAt 20, ttFiber60StateAt 21, ttFiber60StateAt 22, ttFiber60StateAt 23, ttFiber60StateAt 24, ttFiber60StateAt 25, ttFiber60StateAt 26, ttFiber60StateAt 27, ttFiber60StateAt 28, ttFiber60StateAt 29, ttFiber60StateAt 30, ttFiber60StateAt 31, ttFiber60StateAt 32, ttFiber60StateAt 33, ttFiber60StateAt 34, ttFiber60StateAt 35, ttFiber60StateAt 36, ttFiber60StateAt 37, ttFiber60StateAt 38, ttFiber60StateAt 39, ttFiber60StateAt 40, ttFiber60StateAt 41, ttFiber60StateAt 42, ttFiber60StateAt 43, ttFiber60StateAt 44, ttFiber60StateAt 45, ttFiber60StateAt 46, ttFiber60StateAt 47, ttFiber60StateAt 48, ttFiber60StateAt 49, ttFiber60StateAt 50, ttFiber60StateAt 51, ttFiber60StateAt 52, ttFiber60StateAt 53, ttFiber60StateAt 54, ttFiber60StateAt 55, ttFiber60StateAt 56, ttFiber60StateAt 57, ttFiber60StateAt 58, ttFiber60StateAt 59, ttFiber60StateAt 60, ttFiber60StateAt 61, ttFiber60StateAt 62, ttFiber60StateAt 63]
    (chainClosureStep ttWord ttFiber60Prefix13 (chainClosureStep ttWord ttFiber60DirectStates ([ttFiber60StateAt 0])))
    (ttFiber60StateAt 13) ttFiber60State13_in_pass2_prefix13

theorem ttFiber60State0_in_close :
    ttFiber60StateAt 0 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber60DirectStates ttFiber60DirectStates.length
    [ttFiber60StateAt 0] (ttFiber60StateAt 0) (by simp)

theorem ttFiber60State1_in_close :
    ttFiber60StateAt 1 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 1 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 1) ttFiber60State1_in_pass1_full

theorem ttFiber60State2_in_close :
    ttFiber60StateAt 2 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 2 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 2) ttFiber60State2_in_pass1_full

theorem ttFiber60State3_in_close :
    ttFiber60StateAt 3 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 3 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 3) ttFiber60State3_in_pass1_full

theorem ttFiber60State4_in_close :
    ttFiber60StateAt 4 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 4 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 4) ttFiber60State4_in_pass1_full

theorem ttFiber60State5_in_close :
    ttFiber60StateAt 5 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 5 ∈ closeChainFiber ttWord ttFiber60DirectStates (62 + 2)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber60DirectStates 62
    [ttFiber60StateAt 0] (ttFiber60StateAt 5) ttFiber60FirstPassGrows
    ttFiber60State5_in_pass2_full

theorem ttFiber60State6_in_close :
    ttFiber60StateAt 6 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 6 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 6) ttFiber60State6_in_pass1_full

theorem ttFiber60State7_in_close :
    ttFiber60StateAt 7 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 7 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 7) ttFiber60State7_in_pass1_full

theorem ttFiber60State8_in_close :
    ttFiber60StateAt 8 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 8 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 8) ttFiber60State8_in_pass1_full

theorem ttFiber60State9_in_close :
    ttFiber60StateAt 9 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 9 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 9) ttFiber60State9_in_pass1_full

theorem ttFiber60State10_in_close :
    ttFiber60StateAt 10 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 10 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 10) ttFiber60State10_in_pass1_full

theorem ttFiber60State11_in_close :
    ttFiber60StateAt 11 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 11 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 11) ttFiber60State11_in_pass1_full

theorem ttFiber60State12_in_close :
    ttFiber60StateAt 12 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 12 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 12) ttFiber60State12_in_pass1_full

theorem ttFiber60State13_in_close :
    ttFiber60StateAt 13 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 13 ∈ closeChainFiber ttWord ttFiber60DirectStates (62 + 2)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber60DirectStates 62
    [ttFiber60StateAt 0] (ttFiber60StateAt 13) ttFiber60FirstPassGrows
    ttFiber60State13_in_pass2_full

theorem ttFiber60State14_in_close :
    ttFiber60StateAt 14 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 14 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 14) ttFiber60State14_in_pass1_full

theorem ttFiber60State15_in_close :
    ttFiber60StateAt 15 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 15 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 15) ttFiber60State15_in_pass1_full

theorem ttFiber60State16_in_close :
    ttFiber60StateAt 16 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 16 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 16) ttFiber60State16_in_pass1_full

theorem ttFiber60State17_in_close :
    ttFiber60StateAt 17 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 17 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 17) ttFiber60State17_in_pass1_full

theorem ttFiber60State18_in_close :
    ttFiber60StateAt 18 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 18 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 18) ttFiber60State18_in_pass1_full

theorem ttFiber60State19_in_close :
    ttFiber60StateAt 19 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 19 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 19) ttFiber60State19_in_pass1_full

theorem ttFiber60State20_in_close :
    ttFiber60StateAt 20 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 20 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 20) ttFiber60State20_in_pass1_full

theorem ttFiber60State21_in_close :
    ttFiber60StateAt 21 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 21 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 21) ttFiber60State21_in_pass1_full

theorem ttFiber60State22_in_close :
    ttFiber60StateAt 22 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 22 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 22) ttFiber60State22_in_pass1_full

theorem ttFiber60State23_in_close :
    ttFiber60StateAt 23 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 23 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 23) ttFiber60State23_in_pass1_full

theorem ttFiber60State24_in_close :
    ttFiber60StateAt 24 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 24 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 24) ttFiber60State24_in_pass1_full

theorem ttFiber60State25_in_close :
    ttFiber60StateAt 25 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 25 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 25) ttFiber60State25_in_pass1_full

theorem ttFiber60State26_in_close :
    ttFiber60StateAt 26 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 26 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 26) ttFiber60State26_in_pass1_full

theorem ttFiber60State27_in_close :
    ttFiber60StateAt 27 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 27 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 27) ttFiber60State27_in_pass1_full

theorem ttFiber60State28_in_close :
    ttFiber60StateAt 28 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 28 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 28) ttFiber60State28_in_pass1_full

theorem ttFiber60State29_in_close :
    ttFiber60StateAt 29 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 29 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 29) ttFiber60State29_in_pass1_full

theorem ttFiber60State30_in_close :
    ttFiber60StateAt 30 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 30 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 30) ttFiber60State30_in_pass1_full

theorem ttFiber60State31_in_close :
    ttFiber60StateAt 31 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 31 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 31) ttFiber60State31_in_pass1_full

theorem ttFiber60State32_in_close :
    ttFiber60StateAt 32 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 32 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 32) ttFiber60State32_in_pass1_full

theorem ttFiber60State33_in_close :
    ttFiber60StateAt 33 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 33 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 33) ttFiber60State33_in_pass1_full

theorem ttFiber60State34_in_close :
    ttFiber60StateAt 34 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 34 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 34) ttFiber60State34_in_pass1_full

theorem ttFiber60State35_in_close :
    ttFiber60StateAt 35 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 35 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 35) ttFiber60State35_in_pass1_full

theorem ttFiber60State36_in_close :
    ttFiber60StateAt 36 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 36 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 36) ttFiber60State36_in_pass1_full

theorem ttFiber60State37_in_close :
    ttFiber60StateAt 37 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 37 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 37) ttFiber60State37_in_pass1_full

theorem ttFiber60State38_in_close :
    ttFiber60StateAt 38 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 38 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 38) ttFiber60State38_in_pass1_full

theorem ttFiber60State39_in_close :
    ttFiber60StateAt 39 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 39 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 39) ttFiber60State39_in_pass1_full

theorem ttFiber60State40_in_close :
    ttFiber60StateAt 40 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 40 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 40) ttFiber60State40_in_pass1_full

theorem ttFiber60State41_in_close :
    ttFiber60StateAt 41 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 41 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 41) ttFiber60State41_in_pass1_full

theorem ttFiber60State42_in_close :
    ttFiber60StateAt 42 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 42 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 42) ttFiber60State42_in_pass1_full

theorem ttFiber60State43_in_close :
    ttFiber60StateAt 43 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 43 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 43) ttFiber60State43_in_pass1_full

theorem ttFiber60State44_in_close :
    ttFiber60StateAt 44 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 44 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 44) ttFiber60State44_in_pass1_full

theorem ttFiber60State45_in_close :
    ttFiber60StateAt 45 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 45 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 45) ttFiber60State45_in_pass1_full

theorem ttFiber60State46_in_close :
    ttFiber60StateAt 46 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 46 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 46) ttFiber60State46_in_pass1_full

theorem ttFiber60State47_in_close :
    ttFiber60StateAt 47 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 47 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 47) ttFiber60State47_in_pass1_full

theorem ttFiber60State48_in_close :
    ttFiber60StateAt 48 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 48 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 48) ttFiber60State48_in_pass1_full

theorem ttFiber60State49_in_close :
    ttFiber60StateAt 49 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 49 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 49) ttFiber60State49_in_pass1_full

theorem ttFiber60State50_in_close :
    ttFiber60StateAt 50 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 50 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 50) ttFiber60State50_in_pass1_full

theorem ttFiber60State51_in_close :
    ttFiber60StateAt 51 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 51 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 51) ttFiber60State51_in_pass1_full

theorem ttFiber60State52_in_close :
    ttFiber60StateAt 52 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 52 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 52) ttFiber60State52_in_pass1_full

theorem ttFiber60State53_in_close :
    ttFiber60StateAt 53 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 53 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 53) ttFiber60State53_in_pass1_full

theorem ttFiber60State54_in_close :
    ttFiber60StateAt 54 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 54 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 54) ttFiber60State54_in_pass1_full

theorem ttFiber60State55_in_close :
    ttFiber60StateAt 55 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 55 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 55) ttFiber60State55_in_pass1_full

theorem ttFiber60State56_in_close :
    ttFiber60StateAt 56 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 56 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 56) ttFiber60State56_in_pass1_full

theorem ttFiber60State57_in_close :
    ttFiber60StateAt 57 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 57 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 57) ttFiber60State57_in_pass1_full

theorem ttFiber60State58_in_close :
    ttFiber60StateAt 58 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 58 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 58) ttFiber60State58_in_pass1_full

theorem ttFiber60State59_in_close :
    ttFiber60StateAt 59 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 59 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 59) ttFiber60State59_in_pass1_full

theorem ttFiber60State60_in_close :
    ttFiber60StateAt 60 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 60 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 60) ttFiber60State60_in_pass1_full

theorem ttFiber60State61_in_close :
    ttFiber60StateAt 61 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 61 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 61) ttFiber60State61_in_pass1_full

theorem ttFiber60State62_in_close :
    ttFiber60StateAt 62 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 62 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 62) ttFiber60State62_in_pass1_full

theorem ttFiber60State63_in_close :
    ttFiber60StateAt 63 ∈
      closeChainFiber ttWord ttFiber60DirectStates ttFiber60DirectStates.length
        [ttFiber60StateAt 0] := by
  change ttFiber60StateAt 63 ∈ closeChainFiber ttWord ttFiber60DirectStates (63 + 1)
    [ttFiber60StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber60DirectStates 63
    [ttFiber60StateAt 0] (ttFiber60StateAt 63) ttFiber60State63_in_pass1_full

theorem ttFiber60DirectConnected :
    chainFiberConnected ttWord ttFiber60DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber60DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber60State0_in_close
  · subst state
    exact ttFiber60State1_in_close
  · subst state
    exact ttFiber60State2_in_close
  · subst state
    exact ttFiber60State3_in_close
  · subst state
    exact ttFiber60State4_in_close
  · subst state
    exact ttFiber60State5_in_close
  · subst state
    exact ttFiber60State6_in_close
  · subst state
    exact ttFiber60State7_in_close
  · subst state
    exact ttFiber60State8_in_close
  · subst state
    exact ttFiber60State9_in_close
  · subst state
    exact ttFiber60State10_in_close
  · subst state
    exact ttFiber60State11_in_close
  · subst state
    exact ttFiber60State12_in_close
  · subst state
    exact ttFiber60State13_in_close
  · subst state
    exact ttFiber60State14_in_close
  · subst state
    exact ttFiber60State15_in_close
  · subst state
    exact ttFiber60State16_in_close
  · subst state
    exact ttFiber60State17_in_close
  · subst state
    exact ttFiber60State18_in_close
  · subst state
    exact ttFiber60State19_in_close
  · subst state
    exact ttFiber60State20_in_close
  · subst state
    exact ttFiber60State21_in_close
  · subst state
    exact ttFiber60State22_in_close
  · subst state
    exact ttFiber60State23_in_close
  · subst state
    exact ttFiber60State24_in_close
  · subst state
    exact ttFiber60State25_in_close
  · subst state
    exact ttFiber60State26_in_close
  · subst state
    exact ttFiber60State27_in_close
  · subst state
    exact ttFiber60State28_in_close
  · subst state
    exact ttFiber60State29_in_close
  · subst state
    exact ttFiber60State30_in_close
  · subst state
    exact ttFiber60State31_in_close
  · subst state
    exact ttFiber60State32_in_close
  · subst state
    exact ttFiber60State33_in_close
  · subst state
    exact ttFiber60State34_in_close
  · subst state
    exact ttFiber60State35_in_close
  · subst state
    exact ttFiber60State36_in_close
  · subst state
    exact ttFiber60State37_in_close
  · subst state
    exact ttFiber60State38_in_close
  · subst state
    exact ttFiber60State39_in_close
  · subst state
    exact ttFiber60State40_in_close
  · subst state
    exact ttFiber60State41_in_close
  · subst state
    exact ttFiber60State42_in_close
  · subst state
    exact ttFiber60State43_in_close
  · subst state
    exact ttFiber60State44_in_close
  · subst state
    exact ttFiber60State45_in_close
  · subst state
    exact ttFiber60State46_in_close
  · subst state
    exact ttFiber60State47_in_close
  · subst state
    exact ttFiber60State48_in_close
  · subst state
    exact ttFiber60State49_in_close
  · subst state
    exact ttFiber60State50_in_close
  · subst state
    exact ttFiber60State51_in_close
  · subst state
    exact ttFiber60State52_in_close
  · subst state
    exact ttFiber60State53_in_close
  · subst state
    exact ttFiber60State54_in_close
  · subst state
    exact ttFiber60State55_in_close
  · subst state
    exact ttFiber60State56_in_close
  · subst state
    exact ttFiber60State57_in_close
  · subst state
    exact ttFiber60State58_in_close
  · subst state
    exact ttFiber60State59_in_close
  · subst state
    exact ttFiber60State60_in_close
  · subst state
    exact ttFiber60State61_in_close
  · subst state
    exact ttFiber60State62_in_close
  · subst state
    exact ttFiber60State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
