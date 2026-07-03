import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber44

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber44StateAt (i : Nat) : List TauState :=
  directStates (ttFiber44RowAt i).sourceLeft (ttFiber44RowAt i).sourceRight

def ttFiber44DirectStates : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]

def ttFiber44Prefix0 : List (List TauState) :=
  [ttFiber44StateAt 0]

def ttFiber44Prefix1 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1]

def ttFiber44Prefix2 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2]

def ttFiber44Prefix3 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3]

def ttFiber44Prefix4 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4]

def ttFiber44Prefix5 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5]

def ttFiber44Prefix6 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6]

def ttFiber44Prefix7 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7]

def ttFiber44Prefix8 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8]

def ttFiber44Prefix9 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9]

def ttFiber44Prefix10 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10]

def ttFiber44Prefix11 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11]

def ttFiber44Prefix12 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12]

def ttFiber44Prefix13 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13]

def ttFiber44Prefix14 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14]

def ttFiber44Prefix15 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15]

def ttFiber44Prefix16 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16]

def ttFiber44Prefix17 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17]

def ttFiber44Prefix18 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18]

def ttFiber44Prefix19 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19]

def ttFiber44Prefix20 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20]

def ttFiber44Prefix21 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21]

def ttFiber44Prefix22 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22]

def ttFiber44Prefix23 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23]

def ttFiber44Prefix24 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24]

def ttFiber44Prefix25 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25]

def ttFiber44Prefix26 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26]

def ttFiber44Prefix27 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27]

def ttFiber44Prefix28 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28]

def ttFiber44Prefix29 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29]

def ttFiber44Prefix30 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30]

def ttFiber44Prefix31 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31]

def ttFiber44Prefix32 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32]

def ttFiber44Prefix33 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33]

def ttFiber44Prefix34 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34]

def ttFiber44Prefix35 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35]

def ttFiber44Prefix36 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36]

def ttFiber44Prefix37 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37]

def ttFiber44Prefix38 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38]

def ttFiber44Prefix39 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39]

def ttFiber44Prefix40 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40]

def ttFiber44Prefix41 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41]

def ttFiber44Prefix42 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42]

def ttFiber44Prefix43 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43]

def ttFiber44Prefix44 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44]

def ttFiber44Prefix45 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45]

def ttFiber44Prefix46 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46]

def ttFiber44Prefix47 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47]

def ttFiber44Prefix48 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48]

def ttFiber44Prefix49 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49]

def ttFiber44Prefix50 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50]

def ttFiber44Prefix51 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51]

def ttFiber44Prefix52 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52]

def ttFiber44Prefix53 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53]

def ttFiber44Prefix54 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54]

def ttFiber44Prefix55 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55]

def ttFiber44Prefix56 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56]

def ttFiber44Prefix57 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57]

def ttFiber44Prefix58 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58]

def ttFiber44Prefix59 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59]

def ttFiber44Prefix60 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60]

def ttFiber44Prefix61 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61]

def ttFiber44Prefix62 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62]

def ttFiber44Prefix63 : List (List TauState) :=
  [ttFiber44StateAt 0, ttFiber44StateAt 1, ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]

theorem ttFiber44ReverseRow_1_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk0] at h
  exact h.2

theorem ttFiber44ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 1)
      (ttFiber44RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 1) (by decide) ttFiber44ReverseRow_1_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_2_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk1] at h
  exact h.1

theorem ttFiber44ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 2)
      (ttFiber44RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 2) (by decide) ttFiber44ReverseRow_2_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_3_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk1] at h
  exact h.2

theorem ttFiber44ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 3)
      (ttFiber44RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 3) (by decide) ttFiber44ReverseRow_3_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_4_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk2] at h
  exact h.1

theorem ttFiber44ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 4)
      (ttFiber44RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 4) (by decide) ttFiber44ReverseRow_4_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_5_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk2] at h
  exact h.2

theorem ttFiber44ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 5)
      (ttFiber44RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 5) (by decide) ttFiber44ReverseRow_5_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_6_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk3] at h
  exact h.1

theorem ttFiber44ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 6)
      (ttFiber44RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 6) (by decide) ttFiber44ReverseRow_6_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_7_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk3] at h
  exact h.2

theorem ttFiber44ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 7)
      (ttFiber44RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 7) (by decide) ttFiber44ReverseRow_7_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_8_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk4] at h
  exact h.1

theorem ttFiber44ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 8)
      (ttFiber44RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 8) (by decide) ttFiber44ReverseRow_8_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_9_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk4] at h
  exact h.2

theorem ttFiber44ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 9)
      (ttFiber44RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 9) (by decide) ttFiber44ReverseRow_9_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_10_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk5] at h
  exact h.1

theorem ttFiber44ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 10)
      (ttFiber44RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 10) (by decide) ttFiber44ReverseRow_10_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_11_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk5] at h
  exact h.2

theorem ttFiber44ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 11)
      (ttFiber44RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 11) (by decide) ttFiber44ReverseRow_11_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_12_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk6] at h
  exact h.1

theorem ttFiber44ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 12)
      (ttFiber44RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 12) (by decide) ttFiber44ReverseRow_12_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_13_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk6] at h
  exact h.2

theorem ttFiber44ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 13)
      (ttFiber44RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 13) (by decide) ttFiber44ReverseRow_13_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_14_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk7] at h
  exact h.1

theorem ttFiber44ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 6) (ttFiber44StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 6) (ttFiber44StateAt 14)
      (ttFiber44RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 14) (by decide) ttFiber44ReverseRow_14_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_15_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk7] at h
  exact h.2

theorem ttFiber44ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 7) (ttFiber44StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 7) (ttFiber44StateAt 15)
      (ttFiber44RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 15) (by decide) ttFiber44ReverseRow_15_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_16_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk8] at h
  exact h.1

theorem ttFiber44ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 20) (ttFiber44StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 20) (ttFiber44StateAt 16)
      (ttFiber44RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 16) (by decide) ttFiber44ReverseRow_16_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_17_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk8] at h
  exact h.2

theorem ttFiber44ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 21) (ttFiber44StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 21) (ttFiber44StateAt 17)
      (ttFiber44RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 17) (by decide) ttFiber44ReverseRow_17_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_18_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk9] at h
  exact h.1

theorem ttFiber44ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 12) (ttFiber44StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 12) (ttFiber44StateAt 18)
      (ttFiber44RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 18) (by decide) ttFiber44ReverseRow_18_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_19_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk9] at h
  exact h.2

theorem ttFiber44ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 13) (ttFiber44StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 13) (ttFiber44StateAt 19)
      (ttFiber44RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 19) (by decide) ttFiber44ReverseRow_19_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_20_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk10] at h
  exact h.1

theorem ttFiber44ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 8) (ttFiber44StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 8) (ttFiber44StateAt 20)
      (ttFiber44RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 20) (by decide) ttFiber44ReverseRow_20_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_21_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk10] at h
  exact h.2

theorem ttFiber44ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 9) (ttFiber44StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 9) (ttFiber44StateAt 21)
      (ttFiber44RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 21) (by decide) ttFiber44ReverseRow_21_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_22_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk11] at h
  exact h.1

theorem ttFiber44ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 10) (ttFiber44StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 10) (ttFiber44StateAt 22)
      (ttFiber44RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 22) (by decide) ttFiber44ReverseRow_22_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_23_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk11] at h
  exact h.2

theorem ttFiber44ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 11) (ttFiber44StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 11) (ttFiber44StateAt 23)
      (ttFiber44RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 23) (by decide) ttFiber44ReverseRow_23_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_24_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk12] at h
  exact h.1

theorem ttFiber44ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 28) (ttFiber44StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 28) (ttFiber44StateAt 24)
      (ttFiber44RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 24) (by decide) ttFiber44ReverseRow_24_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_25_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk12] at h
  exact h.2

theorem ttFiber44ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 29) (ttFiber44StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 29) (ttFiber44StateAt 25)
      (ttFiber44RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 25) (by decide) ttFiber44ReverseRow_25_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_26_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk13] at h
  exact h.1

theorem ttFiber44ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 26)
      (ttFiber44RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 26) (by decide) ttFiber44ReverseRow_26_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_27_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk13] at h
  exact h.2

theorem ttFiber44ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 27)
      (ttFiber44RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 27) (by decide) ttFiber44ReverseRow_27_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_28_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk14] at h
  exact h.1

theorem ttFiber44ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 28)
      (ttFiber44RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 28) (by decide) ttFiber44ReverseRow_28_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_29_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk14] at h
  exact h.2

theorem ttFiber44ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 29)
      (ttFiber44RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 29) (by decide) ttFiber44ReverseRow_29_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_30_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk15] at h
  exact h.1

theorem ttFiber44ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 30)
      (ttFiber44RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 30) (by decide) ttFiber44ReverseRow_30_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_31_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk15] at h
  exact h.2

theorem ttFiber44ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 31)
      (ttFiber44RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 31) (by decide) ttFiber44ReverseRow_31_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_32_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk16] at h
  exact h.1

theorem ttFiber44ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 0) (ttFiber44StateAt 32)
      (ttFiber44RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 32) (by decide) ttFiber44ReverseRow_32_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_33_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk16] at h
  exact h.2

theorem ttFiber44ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 1) (ttFiber44StateAt 33)
      (ttFiber44RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 33) (by decide) ttFiber44ReverseRow_33_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_34_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk17] at h
  exact h.1

theorem ttFiber44ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 2) (ttFiber44StateAt 34)
      (ttFiber44RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 34) (by decide) ttFiber44ReverseRow_34_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_35_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk17] at h
  exact h.2

theorem ttFiber44ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 3) (ttFiber44StateAt 35)
      (ttFiber44RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 35) (by decide) ttFiber44ReverseRow_35_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_36_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk18] at h
  exact h.1

theorem ttFiber44ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 4) (ttFiber44StateAt 36)
      (ttFiber44RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 36) (by decide) ttFiber44ReverseRow_36_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_37_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk18] at h
  exact h.2

theorem ttFiber44ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 5) (ttFiber44StateAt 37)
      (ttFiber44RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 37) (by decide) ttFiber44ReverseRow_37_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_38_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk19] at h
  exact h.1

theorem ttFiber44ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 6) (ttFiber44StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 6) (ttFiber44StateAt 38)
      (ttFiber44RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 38) (by decide) ttFiber44ReverseRow_38_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_39_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk19] at h
  exact h.2

theorem ttFiber44ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 7) (ttFiber44StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 7) (ttFiber44StateAt 39)
      (ttFiber44RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 39) (by decide) ttFiber44ReverseRow_39_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_40_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk20] at h
  exact h.1

theorem ttFiber44ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 8) (ttFiber44StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 8) (ttFiber44StateAt 40)
      (ttFiber44RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 40) (by decide) ttFiber44ReverseRow_40_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_41_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk20] at h
  exact h.2

theorem ttFiber44ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 9) (ttFiber44StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 9) (ttFiber44StateAt 41)
      (ttFiber44RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 41) (by decide) ttFiber44ReverseRow_41_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_42_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk21] at h
  exact h.1

theorem ttFiber44ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 10) (ttFiber44StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 10) (ttFiber44StateAt 42)
      (ttFiber44RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 42) (by decide) ttFiber44ReverseRow_42_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_43_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk21] at h
  exact h.2

theorem ttFiber44ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 11) (ttFiber44StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 11) (ttFiber44StateAt 43)
      (ttFiber44RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 43) (by decide) ttFiber44ReverseRow_43_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_44_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk22] at h
  exact h.1

theorem ttFiber44ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 12) (ttFiber44StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 12) (ttFiber44StateAt 44)
      (ttFiber44RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 44) (by decide) ttFiber44ReverseRow_44_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_45_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk22] at h
  exact h.2

theorem ttFiber44ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 13) (ttFiber44StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 13) (ttFiber44StateAt 45)
      (ttFiber44RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 45) (by decide) ttFiber44ReverseRow_45_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_46_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk23] at h
  exact h.1

theorem ttFiber44ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 14) (ttFiber44StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 14) (ttFiber44StateAt 46)
      (ttFiber44RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 46) (by decide) ttFiber44ReverseRow_46_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_47_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk23] at h
  exact h.2

theorem ttFiber44ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 15) (ttFiber44StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 15) (ttFiber44StateAt 47)
      (ttFiber44RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 47) (by decide) ttFiber44ReverseRow_47_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_48_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk24] at h
  exact h.1

theorem ttFiber44ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 32) (ttFiber44StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 32) (ttFiber44StateAt 48)
      (ttFiber44RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 48) (by decide) ttFiber44ReverseRow_48_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_49_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk24] at h
  exact h.2

theorem ttFiber44ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 33) (ttFiber44StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 33) (ttFiber44StateAt 49)
      (ttFiber44RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 49) (by decide) ttFiber44ReverseRow_49_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_50_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk25] at h
  exact h.1

theorem ttFiber44ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 48) (ttFiber44StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 48) (ttFiber44StateAt 50)
      (ttFiber44RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 50) (by decide) ttFiber44ReverseRow_50_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_51_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk25] at h
  exact h.2

theorem ttFiber44ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 35) (ttFiber44StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 35) (ttFiber44StateAt 51)
      (ttFiber44RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 51) (by decide) ttFiber44ReverseRow_51_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_52_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk26] at h
  exact h.1

theorem ttFiber44ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 36) (ttFiber44StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 36) (ttFiber44StateAt 52)
      (ttFiber44RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 52) (by decide) ttFiber44ReverseRow_52_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_53_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk26] at h
  exact h.2

theorem ttFiber44ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 37) (ttFiber44StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 37) (ttFiber44StateAt 53)
      (ttFiber44RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 53) (by decide) ttFiber44ReverseRow_53_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_54_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk27] at h
  exact h.1

theorem ttFiber44ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 49) (ttFiber44StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 49) (ttFiber44StateAt 54)
      (ttFiber44RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 54) (by decide) ttFiber44ReverseRow_54_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_55_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk27] at h
  exact h.2

theorem ttFiber44ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 48) (ttFiber44StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 48) (ttFiber44StateAt 55)
      (ttFiber44RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 55) (by decide) ttFiber44ReverseRow_55_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_56_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk28] at h
  exact h.1

theorem ttFiber44ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 40) (ttFiber44StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 40) (ttFiber44StateAt 56)
      (ttFiber44RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 56) (by decide) ttFiber44ReverseRow_56_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_57_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk28] at h
  exact h.2

theorem ttFiber44ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 41) (ttFiber44StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 41) (ttFiber44StateAt 57)
      (ttFiber44RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 57) (by decide) ttFiber44ReverseRow_57_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_58_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk29] at h
  exact h.1

theorem ttFiber44ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 26) (ttFiber44StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 26) (ttFiber44StateAt 58)
      (ttFiber44RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 58) (by decide) ttFiber44ReverseRow_58_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_59_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk29] at h
  exact h.2

theorem ttFiber44ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 27) (ttFiber44StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 27) (ttFiber44StateAt 59)
      (ttFiber44RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 59) (by decide) ttFiber44ReverseRow_59_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_60_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk30] at h
  exact h.1

theorem ttFiber44ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 28) (ttFiber44StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 28) (ttFiber44StateAt 60)
      (ttFiber44RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 60) (by decide) ttFiber44ReverseRow_60_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_61_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk30] at h
  exact h.2

theorem ttFiber44ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 29) (ttFiber44StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 29) (ttFiber44StateAt 61)
      (ttFiber44RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 61) (by decide) ttFiber44ReverseRow_61_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_62_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk31] at h
  exact h.1

theorem ttFiber44ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 60) (ttFiber44StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 60) (ttFiber44StateAt 62)
      (ttFiber44RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 62) (by decide) ttFiber44ReverseRow_62_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44ReverseRow_63_ok' :
    directRowReverseValid ttFiber44Key ttFiber44Expected (ttFiber44RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber44Chunk31] at h
  exact h.2

theorem ttFiber44ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber44StateAt 31) (ttFiber44StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber44StateAt 31) (ttFiber44StateAt 63)
      (ttFiber44RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber44Key ttFiber44Expected
      (ttFiber44RowAt 63) (by decide) ttFiber44ReverseRow_63_ok'
    simpa [ttFiber44StateAt, ttFiber44RowAt, ttFiber44Rows, listGetD, directRow] using h

theorem ttFiber44FirstPassGrows :
    ((chainClosureStep ttWord ttFiber44DirectStates [ttFiber44StateAt 0]).length ==
      [ttFiber44StateAt 0].length) = false := by
  have hroot : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44DirectStates [ttFiber44StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber44DirectStates [ttFiber44StateAt 0]
      (ttFiber44StateAt 0) (by simp)
  have hnew : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44DirectStates [ttFiber44StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber44DirectStates [ttFiber44StateAt 0]
      (ttFiber44StateAt 0) (ttFiber44StateAt 1) (by decide) (by simp)
      ttFiber44ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber44DirectStates [ttFiber44StateAt 0])
    (ttFiber44StateAt 0) (ttFiber44StateAt 1) hroot hnew (by decide)

theorem ttFiber44State0_in_pass0_full :
    ttFiber44StateAt 0 ∈ [ttFiber44StateAt 0] := by
  simp

theorem ttFiber44State0_in_pass1_full :
    ttFiber44StateAt 0 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber44DirectStates
    ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full

theorem ttFiber44State1_in_pass1_prefix1 :
    ttFiber44StateAt 1 ∈ chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix0 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix0
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix1 = ttFiber44Prefix0 ++ [ttFiber44StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 1) []
    (chainClosureStep ttWord ttFiber44Prefix0 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep1

theorem ttFiber44State1_in_pass1_full :
    ttFiber44StateAt 1 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix1 ++ [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1

theorem ttFiber44State2_in_pass1_prefix2 :
    ttFiber44StateAt 2 ∈ chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix1 = ttFiber44Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1
  rw [show ttFiber44Prefix2 = ttFiber44Prefix1 ++ [ttFiber44StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 2) []
    (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) hparentBefore ttFiber44ReverseSingleStep2

theorem ttFiber44State2_in_pass1_full :
    ttFiber44StateAt 2 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix2 ++ [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 2) ttFiber44State2_in_pass1_prefix2

theorem ttFiber44State3_in_pass1_prefix3 :
    ttFiber44StateAt 3 ∈ chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix2
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix3 = ttFiber44Prefix2 ++ [ttFiber44StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 3) []
    (chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep3

theorem ttFiber44State3_in_pass1_full :
    ttFiber44StateAt 3 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix3 ++ [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 3) ttFiber44State3_in_pass1_prefix3

theorem ttFiber44State4_in_pass1_prefix4 :
    ttFiber44StateAt 4 ∈ chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix3
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix4 = ttFiber44Prefix3 ++ [ttFiber44StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 4) []
    (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep4

theorem ttFiber44State4_in_pass1_full :
    ttFiber44StateAt 4 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix4 ++ [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 4) ttFiber44State4_in_pass1_prefix4

theorem ttFiber44State5_in_pass1_prefix5 :
    ttFiber44StateAt 5 ∈ chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix4 = ttFiber44Prefix1 ++ [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4]
      (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1
  rw [show ttFiber44Prefix5 = ttFiber44Prefix4 ++ [ttFiber44StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 5) []
    (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) hparentBefore ttFiber44ReverseSingleStep5

theorem ttFiber44State5_in_pass1_full :
    ttFiber44StateAt 5 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix5 ++ [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 5) ttFiber44State5_in_pass1_prefix5

theorem ttFiber44State6_in_pass1_prefix6 :
    ttFiber44StateAt 6 ∈ chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 4 ∈
      chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix5 = ttFiber44Prefix4 ++ [ttFiber44StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 5]
      (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 4) ttFiber44State4_in_pass1_prefix4
  rw [show ttFiber44Prefix6 = ttFiber44Prefix5 ++ [ttFiber44StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 6) []
    (chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 4) hparentBefore ttFiber44ReverseSingleStep6

theorem ttFiber44State6_in_pass1_full :
    ttFiber44StateAt 6 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix6 ++ [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 6) ttFiber44State6_in_pass1_prefix6

theorem ttFiber44State7_in_pass1_prefix7 :
    ttFiber44StateAt 7 ∈ chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 3 ∈
      chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix6 = ttFiber44Prefix3 ++ [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6]
      (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 3) ttFiber44State3_in_pass1_prefix3
  rw [show ttFiber44Prefix7 = ttFiber44Prefix6 ++ [ttFiber44StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 7) []
    (chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 3) hparentBefore ttFiber44ReverseSingleStep7

theorem ttFiber44State7_in_pass1_full :
    ttFiber44StateAt 7 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix7 ++ [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 7) ttFiber44State7_in_pass1_prefix7

theorem ttFiber44State8_in_pass1_prefix8 :
    ttFiber44StateAt 8 ∈ chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix7
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix8 = ttFiber44Prefix7 ++ [ttFiber44StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 8) []
    (chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep8

theorem ttFiber44State8_in_pass1_full :
    ttFiber44StateAt 8 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix8 ++ [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 8) ttFiber44State8_in_pass1_prefix8

theorem ttFiber44State9_in_pass1_prefix9 :
    ttFiber44StateAt 9 ∈ chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix8 = ttFiber44Prefix1 ++ [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8]
      (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1
  rw [show ttFiber44Prefix9 = ttFiber44Prefix8 ++ [ttFiber44StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 9) []
    (chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) hparentBefore ttFiber44ReverseSingleStep9

theorem ttFiber44State9_in_pass1_full :
    ttFiber44StateAt 9 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix9 ++ [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 9) ttFiber44State9_in_pass1_prefix9

theorem ttFiber44State10_in_pass1_prefix10 :
    ttFiber44StateAt 10 ∈ chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 2 ∈
      chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix9 = ttFiber44Prefix2 ++ [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9]
      (chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 2) ttFiber44State2_in_pass1_prefix2
  rw [show ttFiber44Prefix10 = ttFiber44Prefix9 ++ [ttFiber44StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 10) []
    (chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 2) hparentBefore ttFiber44ReverseSingleStep10

theorem ttFiber44State10_in_pass1_full :
    ttFiber44StateAt 10 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix10 ++ [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 10) ttFiber44State10_in_pass1_prefix10

theorem ttFiber44State11_in_pass1_prefix11 :
    ttFiber44StateAt 11 ∈ chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 3 ∈
      chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix10 = ttFiber44Prefix3 ++ [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10]
      (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 3) ttFiber44State3_in_pass1_prefix3
  rw [show ttFiber44Prefix11 = ttFiber44Prefix10 ++ [ttFiber44StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 11) []
    (chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 3) hparentBefore ttFiber44ReverseSingleStep11

theorem ttFiber44State11_in_pass1_full :
    ttFiber44StateAt 11 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix11 ++ [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 11) ttFiber44State11_in_pass1_prefix11

theorem ttFiber44State12_in_pass1_prefix12 :
    ttFiber44StateAt 12 ∈ chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 4 ∈
      chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix11 = ttFiber44Prefix4 ++ [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11]
      (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 4) ttFiber44State4_in_pass1_prefix4
  rw [show ttFiber44Prefix12 = ttFiber44Prefix11 ++ [ttFiber44StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 12) []
    (chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 4) hparentBefore ttFiber44ReverseSingleStep12

theorem ttFiber44State12_in_pass1_full :
    ttFiber44StateAt 12 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix12 ++ [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 12) ttFiber44State12_in_pass1_prefix12

theorem ttFiber44State13_in_pass1_prefix13 :
    ttFiber44StateAt 13 ∈ chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 5 ∈
      chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix12 = ttFiber44Prefix5 ++ [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12]
      (chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 5) ttFiber44State5_in_pass1_prefix5
  rw [show ttFiber44Prefix13 = ttFiber44Prefix12 ++ [ttFiber44StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 13) []
    (chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 5) hparentBefore ttFiber44ReverseSingleStep13

theorem ttFiber44State13_in_pass1_full :
    ttFiber44StateAt 13 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix13 ++ [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 13) ttFiber44State13_in_pass1_prefix13

theorem ttFiber44State14_in_pass1_prefix14 :
    ttFiber44StateAt 14 ∈ chainClosureStep ttWord ttFiber44Prefix14 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 6 ∈
      chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix13 = ttFiber44Prefix6 ++ [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13]
      (chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 6) ttFiber44State6_in_pass1_prefix6
  rw [show ttFiber44Prefix14 = ttFiber44Prefix13 ++ [ttFiber44StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 14) []
    (chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 6) hparentBefore ttFiber44ReverseSingleStep14

theorem ttFiber44State14_in_pass1_full :
    ttFiber44StateAt 14 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix14 ++ [ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix14 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 14) ttFiber44State14_in_pass1_prefix14

theorem ttFiber44State15_in_pass1_prefix15 :
    ttFiber44StateAt 15 ∈ chainClosureStep ttWord ttFiber44Prefix15 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 7 ∈
      chainClosureStep ttWord ttFiber44Prefix14 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix14 = ttFiber44Prefix7 ++ [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14]
      (chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 7) ttFiber44State7_in_pass1_prefix7
  rw [show ttFiber44Prefix15 = ttFiber44Prefix14 ++ [ttFiber44StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 15) []
    (chainClosureStep ttWord ttFiber44Prefix14 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 7) hparentBefore ttFiber44ReverseSingleStep15

theorem ttFiber44State15_in_pass1_full :
    ttFiber44StateAt 15 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix15 ++ [ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix15 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 15) ttFiber44State15_in_pass1_prefix15

theorem ttFiber44State18_in_pass1_prefix18 :
    ttFiber44StateAt 18 ∈ chainClosureStep ttWord ttFiber44Prefix18 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 12 ∈
      chainClosureStep ttWord ttFiber44Prefix17 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix17 = ttFiber44Prefix12 ++ [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17]
      (chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 12) ttFiber44State12_in_pass1_prefix12
  rw [show ttFiber44Prefix18 = ttFiber44Prefix17 ++ [ttFiber44StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 18) []
    (chainClosureStep ttWord ttFiber44Prefix17 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 12) hparentBefore ttFiber44ReverseSingleStep18

theorem ttFiber44State18_in_pass1_full :
    ttFiber44StateAt 18 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix18 ++ [ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix18 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 18) ttFiber44State18_in_pass1_prefix18

theorem ttFiber44State19_in_pass1_prefix19 :
    ttFiber44StateAt 19 ∈ chainClosureStep ttWord ttFiber44Prefix19 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 13 ∈
      chainClosureStep ttWord ttFiber44Prefix18 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix18 = ttFiber44Prefix13 ++ [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18]
      (chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 13) ttFiber44State13_in_pass1_prefix13
  rw [show ttFiber44Prefix19 = ttFiber44Prefix18 ++ [ttFiber44StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 19) []
    (chainClosureStep ttWord ttFiber44Prefix18 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 13) hparentBefore ttFiber44ReverseSingleStep19

theorem ttFiber44State19_in_pass1_full :
    ttFiber44StateAt 19 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix19 ++ [ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix19 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 19) ttFiber44State19_in_pass1_prefix19

theorem ttFiber44State20_in_pass1_prefix20 :
    ttFiber44StateAt 20 ∈ chainClosureStep ttWord ttFiber44Prefix20 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 8 ∈
      chainClosureStep ttWord ttFiber44Prefix19 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix19 = ttFiber44Prefix8 ++ [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19]
      (chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 8) ttFiber44State8_in_pass1_prefix8
  rw [show ttFiber44Prefix20 = ttFiber44Prefix19 ++ [ttFiber44StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 20) []
    (chainClosureStep ttWord ttFiber44Prefix19 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 8) hparentBefore ttFiber44ReverseSingleStep20

theorem ttFiber44State20_in_pass1_full :
    ttFiber44StateAt 20 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix20 ++ [ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix20 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 20) ttFiber44State20_in_pass1_prefix20

theorem ttFiber44State21_in_pass1_prefix21 :
    ttFiber44StateAt 21 ∈ chainClosureStep ttWord ttFiber44Prefix21 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 9 ∈
      chainClosureStep ttWord ttFiber44Prefix20 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix20 = ttFiber44Prefix9 ++ [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20]
      (chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 9) ttFiber44State9_in_pass1_prefix9
  rw [show ttFiber44Prefix21 = ttFiber44Prefix20 ++ [ttFiber44StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 21) []
    (chainClosureStep ttWord ttFiber44Prefix20 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 9) hparentBefore ttFiber44ReverseSingleStep21

theorem ttFiber44State21_in_pass1_full :
    ttFiber44StateAt 21 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix21 ++ [ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix21 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 21) ttFiber44State21_in_pass1_prefix21

theorem ttFiber44State22_in_pass1_prefix22 :
    ttFiber44StateAt 22 ∈ chainClosureStep ttWord ttFiber44Prefix22 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 10 ∈
      chainClosureStep ttWord ttFiber44Prefix21 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix21 = ttFiber44Prefix10 ++ [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21]
      (chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 10) ttFiber44State10_in_pass1_prefix10
  rw [show ttFiber44Prefix22 = ttFiber44Prefix21 ++ [ttFiber44StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 22) []
    (chainClosureStep ttWord ttFiber44Prefix21 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 10) hparentBefore ttFiber44ReverseSingleStep22

theorem ttFiber44State22_in_pass1_full :
    ttFiber44StateAt 22 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix22 ++ [ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix22 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 22) ttFiber44State22_in_pass1_prefix22

theorem ttFiber44State23_in_pass1_prefix23 :
    ttFiber44StateAt 23 ∈ chainClosureStep ttWord ttFiber44Prefix23 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 11 ∈
      chainClosureStep ttWord ttFiber44Prefix22 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix22 = ttFiber44Prefix11 ++ [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22]
      (chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 11) ttFiber44State11_in_pass1_prefix11
  rw [show ttFiber44Prefix23 = ttFiber44Prefix22 ++ [ttFiber44StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 23) []
    (chainClosureStep ttWord ttFiber44Prefix22 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 11) hparentBefore ttFiber44ReverseSingleStep23

theorem ttFiber44State23_in_pass1_full :
    ttFiber44StateAt 23 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix23 ++ [ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix23 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 23) ttFiber44State23_in_pass1_prefix23

theorem ttFiber44State26_in_pass1_prefix26 :
    ttFiber44StateAt 26 ∈ chainClosureStep ttWord ttFiber44Prefix26 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 4 ∈
      chainClosureStep ttWord ttFiber44Prefix25 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix25 = ttFiber44Prefix4 ++ [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25]
      (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 4) ttFiber44State4_in_pass1_prefix4
  rw [show ttFiber44Prefix26 = ttFiber44Prefix25 ++ [ttFiber44StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 26) []
    (chainClosureStep ttWord ttFiber44Prefix25 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 4) hparentBefore ttFiber44ReverseSingleStep26

theorem ttFiber44State26_in_pass1_full :
    ttFiber44StateAt 26 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix26 ++ [ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix26 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 26) ttFiber44State26_in_pass1_prefix26

theorem ttFiber44State27_in_pass1_prefix27 :
    ttFiber44StateAt 27 ∈ chainClosureStep ttWord ttFiber44Prefix27 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 5 ∈
      chainClosureStep ttWord ttFiber44Prefix26 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix26 = ttFiber44Prefix5 ++ [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26]
      (chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 5) ttFiber44State5_in_pass1_prefix5
  rw [show ttFiber44Prefix27 = ttFiber44Prefix26 ++ [ttFiber44StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 27) []
    (chainClosureStep ttWord ttFiber44Prefix26 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 5) hparentBefore ttFiber44ReverseSingleStep27

theorem ttFiber44State27_in_pass1_full :
    ttFiber44StateAt 27 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix27 ++ [ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix27 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 27) ttFiber44State27_in_pass1_prefix27

theorem ttFiber44State28_in_pass1_prefix28 :
    ttFiber44StateAt 28 ∈ chainClosureStep ttWord ttFiber44Prefix28 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix27 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix27
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix28 = ttFiber44Prefix27 ++ [ttFiber44StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 28) []
    (chainClosureStep ttWord ttFiber44Prefix27 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep28

theorem ttFiber44State28_in_pass1_full :
    ttFiber44StateAt 28 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix28 ++ [ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix28 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 28) ttFiber44State28_in_pass1_prefix28

theorem ttFiber44State29_in_pass1_prefix29 :
    ttFiber44StateAt 29 ∈ chainClosureStep ttWord ttFiber44Prefix29 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44Prefix28 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix28 = ttFiber44Prefix1 ++ [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28]
      (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1
  rw [show ttFiber44Prefix29 = ttFiber44Prefix28 ++ [ttFiber44StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 29) []
    (chainClosureStep ttWord ttFiber44Prefix28 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) hparentBefore ttFiber44ReverseSingleStep29

theorem ttFiber44State29_in_pass1_full :
    ttFiber44StateAt 29 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix29 ++ [ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix29 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 29) ttFiber44State29_in_pass1_prefix29

theorem ttFiber44State30_in_pass1_prefix30 :
    ttFiber44StateAt 30 ∈ chainClosureStep ttWord ttFiber44Prefix30 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 2 ∈
      chainClosureStep ttWord ttFiber44Prefix29 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix29 = ttFiber44Prefix2 ++ [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29]
      (chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 2) ttFiber44State2_in_pass1_prefix2
  rw [show ttFiber44Prefix30 = ttFiber44Prefix29 ++ [ttFiber44StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 30) []
    (chainClosureStep ttWord ttFiber44Prefix29 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 2) hparentBefore ttFiber44ReverseSingleStep30

theorem ttFiber44State30_in_pass1_full :
    ttFiber44StateAt 30 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix30 ++ [ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix30 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 30) ttFiber44State30_in_pass1_prefix30

theorem ttFiber44State31_in_pass1_prefix31 :
    ttFiber44StateAt 31 ∈ chainClosureStep ttWord ttFiber44Prefix31 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 3 ∈
      chainClosureStep ttWord ttFiber44Prefix30 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix30 = ttFiber44Prefix3 ++ [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30]
      (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 3) ttFiber44State3_in_pass1_prefix3
  rw [show ttFiber44Prefix31 = ttFiber44Prefix30 ++ [ttFiber44StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 31) []
    (chainClosureStep ttWord ttFiber44Prefix30 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 3) hparentBefore ttFiber44ReverseSingleStep31

theorem ttFiber44State31_in_pass1_full :
    ttFiber44StateAt 31 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix31 ++ [ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix31 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 31) ttFiber44State31_in_pass1_prefix31

theorem ttFiber44State32_in_pass1_prefix32 :
    ttFiber44StateAt 32 ∈ chainClosureStep ttWord ttFiber44Prefix32 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 0 ∈
      chainClosureStep ttWord ttFiber44Prefix31 ([ttFiber44StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix31
      ([ttFiber44StateAt 0]) (ttFiber44StateAt 0) ttFiber44State0_in_pass0_full
  rw [show ttFiber44Prefix32 = ttFiber44Prefix31 ++ [ttFiber44StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 32) []
    (chainClosureStep ttWord ttFiber44Prefix31 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 0) hparentBefore ttFiber44ReverseSingleStep32

theorem ttFiber44State32_in_pass1_full :
    ttFiber44StateAt 32 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix32 ++ [ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix32 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 32) ttFiber44State32_in_pass1_prefix32

theorem ttFiber44State33_in_pass1_prefix33 :
    ttFiber44StateAt 33 ∈ chainClosureStep ttWord ttFiber44Prefix33 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 1 ∈
      chainClosureStep ttWord ttFiber44Prefix32 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix32 = ttFiber44Prefix1 ++ [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 2, ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32]
      (chainClosureStep ttWord ttFiber44Prefix1 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 1) ttFiber44State1_in_pass1_prefix1
  rw [show ttFiber44Prefix33 = ttFiber44Prefix32 ++ [ttFiber44StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 33) []
    (chainClosureStep ttWord ttFiber44Prefix32 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 1) hparentBefore ttFiber44ReverseSingleStep33

theorem ttFiber44State33_in_pass1_full :
    ttFiber44StateAt 33 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix33 ++ [ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix33 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 33) ttFiber44State33_in_pass1_prefix33

theorem ttFiber44State34_in_pass1_prefix34 :
    ttFiber44StateAt 34 ∈ chainClosureStep ttWord ttFiber44Prefix34 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 2 ∈
      chainClosureStep ttWord ttFiber44Prefix33 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix33 = ttFiber44Prefix2 ++ [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 3, ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33]
      (chainClosureStep ttWord ttFiber44Prefix2 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 2) ttFiber44State2_in_pass1_prefix2
  rw [show ttFiber44Prefix34 = ttFiber44Prefix33 ++ [ttFiber44StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 34) []
    (chainClosureStep ttWord ttFiber44Prefix33 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 2) hparentBefore ttFiber44ReverseSingleStep34

theorem ttFiber44State34_in_pass1_full :
    ttFiber44StateAt 34 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix34 ++ [ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix34 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 34) ttFiber44State34_in_pass1_prefix34

theorem ttFiber44State35_in_pass1_prefix35 :
    ttFiber44StateAt 35 ∈ chainClosureStep ttWord ttFiber44Prefix35 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 3 ∈
      chainClosureStep ttWord ttFiber44Prefix34 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix34 = ttFiber44Prefix3 ++ [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 4, ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34]
      (chainClosureStep ttWord ttFiber44Prefix3 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 3) ttFiber44State3_in_pass1_prefix3
  rw [show ttFiber44Prefix35 = ttFiber44Prefix34 ++ [ttFiber44StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 35) []
    (chainClosureStep ttWord ttFiber44Prefix34 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 3) hparentBefore ttFiber44ReverseSingleStep35

theorem ttFiber44State35_in_pass1_full :
    ttFiber44StateAt 35 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix35 ++ [ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix35 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 35) ttFiber44State35_in_pass1_prefix35

theorem ttFiber44State36_in_pass1_prefix36 :
    ttFiber44StateAt 36 ∈ chainClosureStep ttWord ttFiber44Prefix36 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 4 ∈
      chainClosureStep ttWord ttFiber44Prefix35 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix35 = ttFiber44Prefix4 ++ [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 5, ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35]
      (chainClosureStep ttWord ttFiber44Prefix4 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 4) ttFiber44State4_in_pass1_prefix4
  rw [show ttFiber44Prefix36 = ttFiber44Prefix35 ++ [ttFiber44StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 36) []
    (chainClosureStep ttWord ttFiber44Prefix35 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 4) hparentBefore ttFiber44ReverseSingleStep36

theorem ttFiber44State36_in_pass1_full :
    ttFiber44StateAt 36 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix36 ++ [ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix36 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 36) ttFiber44State36_in_pass1_prefix36

theorem ttFiber44State37_in_pass1_prefix37 :
    ttFiber44StateAt 37 ∈ chainClosureStep ttWord ttFiber44Prefix37 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 5 ∈
      chainClosureStep ttWord ttFiber44Prefix36 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix36 = ttFiber44Prefix5 ++ [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 6, ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36]
      (chainClosureStep ttWord ttFiber44Prefix5 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 5) ttFiber44State5_in_pass1_prefix5
  rw [show ttFiber44Prefix37 = ttFiber44Prefix36 ++ [ttFiber44StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 37) []
    (chainClosureStep ttWord ttFiber44Prefix36 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 5) hparentBefore ttFiber44ReverseSingleStep37

theorem ttFiber44State37_in_pass1_full :
    ttFiber44StateAt 37 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix37 ++ [ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix37 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 37) ttFiber44State37_in_pass1_prefix37

theorem ttFiber44State38_in_pass1_prefix38 :
    ttFiber44StateAt 38 ∈ chainClosureStep ttWord ttFiber44Prefix38 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 6 ∈
      chainClosureStep ttWord ttFiber44Prefix37 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix37 = ttFiber44Prefix6 ++ [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 7, ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37]
      (chainClosureStep ttWord ttFiber44Prefix6 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 6) ttFiber44State6_in_pass1_prefix6
  rw [show ttFiber44Prefix38 = ttFiber44Prefix37 ++ [ttFiber44StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 38) []
    (chainClosureStep ttWord ttFiber44Prefix37 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 6) hparentBefore ttFiber44ReverseSingleStep38

theorem ttFiber44State38_in_pass1_full :
    ttFiber44StateAt 38 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix38 ++ [ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix38 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 38) ttFiber44State38_in_pass1_prefix38

theorem ttFiber44State39_in_pass1_prefix39 :
    ttFiber44StateAt 39 ∈ chainClosureStep ttWord ttFiber44Prefix39 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 7 ∈
      chainClosureStep ttWord ttFiber44Prefix38 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix38 = ttFiber44Prefix7 ++ [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 8, ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38]
      (chainClosureStep ttWord ttFiber44Prefix7 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 7) ttFiber44State7_in_pass1_prefix7
  rw [show ttFiber44Prefix39 = ttFiber44Prefix38 ++ [ttFiber44StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 39) []
    (chainClosureStep ttWord ttFiber44Prefix38 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 7) hparentBefore ttFiber44ReverseSingleStep39

theorem ttFiber44State39_in_pass1_full :
    ttFiber44StateAt 39 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix39 ++ [ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix39 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 39) ttFiber44State39_in_pass1_prefix39

theorem ttFiber44State40_in_pass1_prefix40 :
    ttFiber44StateAt 40 ∈ chainClosureStep ttWord ttFiber44Prefix40 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 8 ∈
      chainClosureStep ttWord ttFiber44Prefix39 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix39 = ttFiber44Prefix8 ++ [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 9, ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39]
      (chainClosureStep ttWord ttFiber44Prefix8 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 8) ttFiber44State8_in_pass1_prefix8
  rw [show ttFiber44Prefix40 = ttFiber44Prefix39 ++ [ttFiber44StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 40) []
    (chainClosureStep ttWord ttFiber44Prefix39 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 8) hparentBefore ttFiber44ReverseSingleStep40

theorem ttFiber44State40_in_pass1_full :
    ttFiber44StateAt 40 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix40 ++ [ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix40 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 40) ttFiber44State40_in_pass1_prefix40

theorem ttFiber44State41_in_pass1_prefix41 :
    ttFiber44StateAt 41 ∈ chainClosureStep ttWord ttFiber44Prefix41 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 9 ∈
      chainClosureStep ttWord ttFiber44Prefix40 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix40 = ttFiber44Prefix9 ++ [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 10, ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40]
      (chainClosureStep ttWord ttFiber44Prefix9 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 9) ttFiber44State9_in_pass1_prefix9
  rw [show ttFiber44Prefix41 = ttFiber44Prefix40 ++ [ttFiber44StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 41) []
    (chainClosureStep ttWord ttFiber44Prefix40 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 9) hparentBefore ttFiber44ReverseSingleStep41

theorem ttFiber44State41_in_pass1_full :
    ttFiber44StateAt 41 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix41 ++ [ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix41 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 41) ttFiber44State41_in_pass1_prefix41

theorem ttFiber44State42_in_pass1_prefix42 :
    ttFiber44StateAt 42 ∈ chainClosureStep ttWord ttFiber44Prefix42 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 10 ∈
      chainClosureStep ttWord ttFiber44Prefix41 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix41 = ttFiber44Prefix10 ++ [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 11, ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41]
      (chainClosureStep ttWord ttFiber44Prefix10 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 10) ttFiber44State10_in_pass1_prefix10
  rw [show ttFiber44Prefix42 = ttFiber44Prefix41 ++ [ttFiber44StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 42) []
    (chainClosureStep ttWord ttFiber44Prefix41 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 10) hparentBefore ttFiber44ReverseSingleStep42

theorem ttFiber44State42_in_pass1_full :
    ttFiber44StateAt 42 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix42 ++ [ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix42 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 42) ttFiber44State42_in_pass1_prefix42

theorem ttFiber44State43_in_pass1_prefix43 :
    ttFiber44StateAt 43 ∈ chainClosureStep ttWord ttFiber44Prefix43 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 11 ∈
      chainClosureStep ttWord ttFiber44Prefix42 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix42 = ttFiber44Prefix11 ++ [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 12, ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42]
      (chainClosureStep ttWord ttFiber44Prefix11 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 11) ttFiber44State11_in_pass1_prefix11
  rw [show ttFiber44Prefix43 = ttFiber44Prefix42 ++ [ttFiber44StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 43) []
    (chainClosureStep ttWord ttFiber44Prefix42 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 11) hparentBefore ttFiber44ReverseSingleStep43

theorem ttFiber44State43_in_pass1_full :
    ttFiber44StateAt 43 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix43 ++ [ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix43 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 43) ttFiber44State43_in_pass1_prefix43

theorem ttFiber44State44_in_pass1_prefix44 :
    ttFiber44StateAt 44 ∈ chainClosureStep ttWord ttFiber44Prefix44 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 12 ∈
      chainClosureStep ttWord ttFiber44Prefix43 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix43 = ttFiber44Prefix12 ++ [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 13, ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43]
      (chainClosureStep ttWord ttFiber44Prefix12 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 12) ttFiber44State12_in_pass1_prefix12
  rw [show ttFiber44Prefix44 = ttFiber44Prefix43 ++ [ttFiber44StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 44) []
    (chainClosureStep ttWord ttFiber44Prefix43 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 12) hparentBefore ttFiber44ReverseSingleStep44

theorem ttFiber44State44_in_pass1_full :
    ttFiber44StateAt 44 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix44 ++ [ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix44 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 44) ttFiber44State44_in_pass1_prefix44

theorem ttFiber44State45_in_pass1_prefix45 :
    ttFiber44StateAt 45 ∈ chainClosureStep ttWord ttFiber44Prefix45 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 13 ∈
      chainClosureStep ttWord ttFiber44Prefix44 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix44 = ttFiber44Prefix13 ++ [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 14, ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44]
      (chainClosureStep ttWord ttFiber44Prefix13 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 13) ttFiber44State13_in_pass1_prefix13
  rw [show ttFiber44Prefix45 = ttFiber44Prefix44 ++ [ttFiber44StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 45) []
    (chainClosureStep ttWord ttFiber44Prefix44 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 13) hparentBefore ttFiber44ReverseSingleStep45

theorem ttFiber44State45_in_pass1_full :
    ttFiber44StateAt 45 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix45 ++ [ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix45 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 45) ttFiber44State45_in_pass1_prefix45

theorem ttFiber44State46_in_pass1_prefix46 :
    ttFiber44StateAt 46 ∈ chainClosureStep ttWord ttFiber44Prefix46 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 14 ∈
      chainClosureStep ttWord ttFiber44Prefix45 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix45 = ttFiber44Prefix14 ++ [ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 15, ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45]
      (chainClosureStep ttWord ttFiber44Prefix14 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 14) ttFiber44State14_in_pass1_prefix14
  rw [show ttFiber44Prefix46 = ttFiber44Prefix45 ++ [ttFiber44StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 46) []
    (chainClosureStep ttWord ttFiber44Prefix45 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 14) hparentBefore ttFiber44ReverseSingleStep46

theorem ttFiber44State46_in_pass1_full :
    ttFiber44StateAt 46 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix46 ++ [ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix46 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 46) ttFiber44State46_in_pass1_prefix46

theorem ttFiber44State47_in_pass1_prefix47 :
    ttFiber44StateAt 47 ∈ chainClosureStep ttWord ttFiber44Prefix47 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 15 ∈
      chainClosureStep ttWord ttFiber44Prefix46 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix46 = ttFiber44Prefix15 ++ [ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 16, ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46]
      (chainClosureStep ttWord ttFiber44Prefix15 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 15) ttFiber44State15_in_pass1_prefix15
  rw [show ttFiber44Prefix47 = ttFiber44Prefix46 ++ [ttFiber44StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 47) []
    (chainClosureStep ttWord ttFiber44Prefix46 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 15) hparentBefore ttFiber44ReverseSingleStep47

theorem ttFiber44State47_in_pass1_full :
    ttFiber44StateAt 47 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix47 ++ [ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix47 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 47) ttFiber44State47_in_pass1_prefix47

theorem ttFiber44State48_in_pass1_prefix48 :
    ttFiber44StateAt 48 ∈ chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 32 ∈
      chainClosureStep ttWord ttFiber44Prefix47 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix47 = ttFiber44Prefix32 ++ [ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47]
      (chainClosureStep ttWord ttFiber44Prefix32 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 32) ttFiber44State32_in_pass1_prefix32
  rw [show ttFiber44Prefix48 = ttFiber44Prefix47 ++ [ttFiber44StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 48) []
    (chainClosureStep ttWord ttFiber44Prefix47 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 32) hparentBefore ttFiber44ReverseSingleStep48

theorem ttFiber44State48_in_pass1_full :
    ttFiber44StateAt 48 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix48 ++ [ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 48) ttFiber44State48_in_pass1_prefix48

theorem ttFiber44State49_in_pass1_prefix49 :
    ttFiber44StateAt 49 ∈ chainClosureStep ttWord ttFiber44Prefix49 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 33 ∈
      chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix48 = ttFiber44Prefix33 ++ [ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48]
      (chainClosureStep ttWord ttFiber44Prefix33 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 33) ttFiber44State33_in_pass1_prefix33
  rw [show ttFiber44Prefix49 = ttFiber44Prefix48 ++ [ttFiber44StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 49) []
    (chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 33) hparentBefore ttFiber44ReverseSingleStep49

theorem ttFiber44State49_in_pass1_full :
    ttFiber44StateAt 49 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix49 ++ [ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix49 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 49) ttFiber44State49_in_pass1_prefix49

theorem ttFiber44State50_in_pass1_prefix50 :
    ttFiber44StateAt 50 ∈ chainClosureStep ttWord ttFiber44Prefix50 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 48 ∈
      chainClosureStep ttWord ttFiber44Prefix49 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix49 = ttFiber44Prefix48 ++ [ttFiber44StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 49]
      (chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 48) ttFiber44State48_in_pass1_prefix48
  rw [show ttFiber44Prefix50 = ttFiber44Prefix49 ++ [ttFiber44StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 50) []
    (chainClosureStep ttWord ttFiber44Prefix49 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 48) hparentBefore ttFiber44ReverseSingleStep50

theorem ttFiber44State50_in_pass1_full :
    ttFiber44StateAt 50 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix50 ++ [ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix50 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 50) ttFiber44State50_in_pass1_prefix50

theorem ttFiber44State51_in_pass1_prefix51 :
    ttFiber44StateAt 51 ∈ chainClosureStep ttWord ttFiber44Prefix51 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 35 ∈
      chainClosureStep ttWord ttFiber44Prefix50 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix50 = ttFiber44Prefix35 ++ [ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50]
      (chainClosureStep ttWord ttFiber44Prefix35 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 35) ttFiber44State35_in_pass1_prefix35
  rw [show ttFiber44Prefix51 = ttFiber44Prefix50 ++ [ttFiber44StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 51) []
    (chainClosureStep ttWord ttFiber44Prefix50 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 35) hparentBefore ttFiber44ReverseSingleStep51

theorem ttFiber44State51_in_pass1_full :
    ttFiber44StateAt 51 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix51 ++ [ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix51 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 51) ttFiber44State51_in_pass1_prefix51

theorem ttFiber44State52_in_pass1_prefix52 :
    ttFiber44StateAt 52 ∈ chainClosureStep ttWord ttFiber44Prefix52 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 36 ∈
      chainClosureStep ttWord ttFiber44Prefix51 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix51 = ttFiber44Prefix36 ++ [ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51]
      (chainClosureStep ttWord ttFiber44Prefix36 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 36) ttFiber44State36_in_pass1_prefix36
  rw [show ttFiber44Prefix52 = ttFiber44Prefix51 ++ [ttFiber44StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 52) []
    (chainClosureStep ttWord ttFiber44Prefix51 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 36) hparentBefore ttFiber44ReverseSingleStep52

theorem ttFiber44State52_in_pass1_full :
    ttFiber44StateAt 52 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix52 ++ [ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix52 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 52) ttFiber44State52_in_pass1_prefix52

theorem ttFiber44State53_in_pass1_prefix53 :
    ttFiber44StateAt 53 ∈ chainClosureStep ttWord ttFiber44Prefix53 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 37 ∈
      chainClosureStep ttWord ttFiber44Prefix52 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix52 = ttFiber44Prefix37 ++ [ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52]
      (chainClosureStep ttWord ttFiber44Prefix37 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 37) ttFiber44State37_in_pass1_prefix37
  rw [show ttFiber44Prefix53 = ttFiber44Prefix52 ++ [ttFiber44StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 53) []
    (chainClosureStep ttWord ttFiber44Prefix52 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 37) hparentBefore ttFiber44ReverseSingleStep53

theorem ttFiber44State53_in_pass1_full :
    ttFiber44StateAt 53 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix53 ++ [ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix53 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 53) ttFiber44State53_in_pass1_prefix53

theorem ttFiber44State54_in_pass1_prefix54 :
    ttFiber44StateAt 54 ∈ chainClosureStep ttWord ttFiber44Prefix54 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 49 ∈
      chainClosureStep ttWord ttFiber44Prefix53 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix53 = ttFiber44Prefix49 ++ [ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53]
      (chainClosureStep ttWord ttFiber44Prefix49 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 49) ttFiber44State49_in_pass1_prefix49
  rw [show ttFiber44Prefix54 = ttFiber44Prefix53 ++ [ttFiber44StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 54) []
    (chainClosureStep ttWord ttFiber44Prefix53 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 49) hparentBefore ttFiber44ReverseSingleStep54

theorem ttFiber44State54_in_pass1_full :
    ttFiber44StateAt 54 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix54 ++ [ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix54 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 54) ttFiber44State54_in_pass1_prefix54

theorem ttFiber44State55_in_pass1_prefix55 :
    ttFiber44StateAt 55 ∈ chainClosureStep ttWord ttFiber44Prefix55 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 48 ∈
      chainClosureStep ttWord ttFiber44Prefix54 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix54 = ttFiber44Prefix48 ++ [ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54]
      (chainClosureStep ttWord ttFiber44Prefix48 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 48) ttFiber44State48_in_pass1_prefix48
  rw [show ttFiber44Prefix55 = ttFiber44Prefix54 ++ [ttFiber44StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 55) []
    (chainClosureStep ttWord ttFiber44Prefix54 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 48) hparentBefore ttFiber44ReverseSingleStep55

theorem ttFiber44State55_in_pass1_full :
    ttFiber44StateAt 55 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix55 ++ [ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix55 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 55) ttFiber44State55_in_pass1_prefix55

theorem ttFiber44State56_in_pass1_prefix56 :
    ttFiber44StateAt 56 ∈ chainClosureStep ttWord ttFiber44Prefix56 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 40 ∈
      chainClosureStep ttWord ttFiber44Prefix55 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix55 = ttFiber44Prefix40 ++ [ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55]
      (chainClosureStep ttWord ttFiber44Prefix40 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 40) ttFiber44State40_in_pass1_prefix40
  rw [show ttFiber44Prefix56 = ttFiber44Prefix55 ++ [ttFiber44StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 56) []
    (chainClosureStep ttWord ttFiber44Prefix55 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 40) hparentBefore ttFiber44ReverseSingleStep56

theorem ttFiber44State56_in_pass1_full :
    ttFiber44StateAt 56 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix56 ++ [ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix56 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 56) ttFiber44State56_in_pass1_prefix56

theorem ttFiber44State57_in_pass1_prefix57 :
    ttFiber44StateAt 57 ∈ chainClosureStep ttWord ttFiber44Prefix57 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 41 ∈
      chainClosureStep ttWord ttFiber44Prefix56 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix56 = ttFiber44Prefix41 ++ [ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56]
      (chainClosureStep ttWord ttFiber44Prefix41 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 41) ttFiber44State41_in_pass1_prefix41
  rw [show ttFiber44Prefix57 = ttFiber44Prefix56 ++ [ttFiber44StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 57) []
    (chainClosureStep ttWord ttFiber44Prefix56 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 41) hparentBefore ttFiber44ReverseSingleStep57

theorem ttFiber44State57_in_pass1_full :
    ttFiber44StateAt 57 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix57 ++ [ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix57 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 57) ttFiber44State57_in_pass1_prefix57

theorem ttFiber44State58_in_pass1_prefix58 :
    ttFiber44StateAt 58 ∈ chainClosureStep ttWord ttFiber44Prefix58 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 26 ∈
      chainClosureStep ttWord ttFiber44Prefix57 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix57 = ttFiber44Prefix26 ++ [ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57]
      (chainClosureStep ttWord ttFiber44Prefix26 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 26) ttFiber44State26_in_pass1_prefix26
  rw [show ttFiber44Prefix58 = ttFiber44Prefix57 ++ [ttFiber44StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 58) []
    (chainClosureStep ttWord ttFiber44Prefix57 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 26) hparentBefore ttFiber44ReverseSingleStep58

theorem ttFiber44State58_in_pass1_full :
    ttFiber44StateAt 58 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix58 ++ [ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix58 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 58) ttFiber44State58_in_pass1_prefix58

theorem ttFiber44State59_in_pass1_prefix59 :
    ttFiber44StateAt 59 ∈ chainClosureStep ttWord ttFiber44Prefix59 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 27 ∈
      chainClosureStep ttWord ttFiber44Prefix58 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix58 = ttFiber44Prefix27 ++ [ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58]
      (chainClosureStep ttWord ttFiber44Prefix27 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 27) ttFiber44State27_in_pass1_prefix27
  rw [show ttFiber44Prefix59 = ttFiber44Prefix58 ++ [ttFiber44StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 59) []
    (chainClosureStep ttWord ttFiber44Prefix58 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 27) hparentBefore ttFiber44ReverseSingleStep59

theorem ttFiber44State59_in_pass1_full :
    ttFiber44StateAt 59 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix59 ++ [ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix59 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 59) ttFiber44State59_in_pass1_prefix59

theorem ttFiber44State60_in_pass1_prefix60 :
    ttFiber44StateAt 60 ∈ chainClosureStep ttWord ttFiber44Prefix60 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 28 ∈
      chainClosureStep ttWord ttFiber44Prefix59 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix59 = ttFiber44Prefix28 ++ [ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59]
      (chainClosureStep ttWord ttFiber44Prefix28 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 28) ttFiber44State28_in_pass1_prefix28
  rw [show ttFiber44Prefix60 = ttFiber44Prefix59 ++ [ttFiber44StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 60) []
    (chainClosureStep ttWord ttFiber44Prefix59 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 28) hparentBefore ttFiber44ReverseSingleStep60

theorem ttFiber44State60_in_pass1_full :
    ttFiber44StateAt 60 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix60 ++ [ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix60 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 60) ttFiber44State60_in_pass1_prefix60

theorem ttFiber44State61_in_pass1_prefix61 :
    ttFiber44StateAt 61 ∈ chainClosureStep ttWord ttFiber44Prefix61 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 29 ∈
      chainClosureStep ttWord ttFiber44Prefix60 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix60 = ttFiber44Prefix29 ++ [ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60]
      (chainClosureStep ttWord ttFiber44Prefix29 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 29) ttFiber44State29_in_pass1_prefix29
  rw [show ttFiber44Prefix61 = ttFiber44Prefix60 ++ [ttFiber44StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 61) []
    (chainClosureStep ttWord ttFiber44Prefix60 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 29) hparentBefore ttFiber44ReverseSingleStep61

theorem ttFiber44State61_in_pass1_full :
    ttFiber44StateAt 61 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix61 ++ [ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix61 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 61) ttFiber44State61_in_pass1_prefix61

theorem ttFiber44State62_in_pass1_prefix62 :
    ttFiber44StateAt 62 ∈ chainClosureStep ttWord ttFiber44Prefix62 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 60 ∈
      chainClosureStep ttWord ttFiber44Prefix61 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix61 = ttFiber44Prefix60 ++ [ttFiber44StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 61]
      (chainClosureStep ttWord ttFiber44Prefix60 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 60) ttFiber44State60_in_pass1_prefix60
  rw [show ttFiber44Prefix62 = ttFiber44Prefix61 ++ [ttFiber44StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 62) []
    (chainClosureStep ttWord ttFiber44Prefix61 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 60) hparentBefore ttFiber44ReverseSingleStep62

theorem ttFiber44State62_in_pass1_full :
    ttFiber44StateAt 62 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix62 ++ [ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix62 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 62) ttFiber44State62_in_pass1_prefix62

theorem ttFiber44State63_in_pass1_prefix63 :
    ttFiber44StateAt 63 ∈ chainClosureStep ttWord ttFiber44Prefix63 ([ttFiber44StateAt 0]) := by
  have hparentBefore : ttFiber44StateAt 31 ∈
      chainClosureStep ttWord ttFiber44Prefix62 ([ttFiber44StateAt 0]) := by
    rw [show ttFiber44Prefix62 = ttFiber44Prefix31 ++ [ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62]
      (chainClosureStep ttWord ttFiber44Prefix31 ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 31) ttFiber44State31_in_pass1_prefix31
  rw [show ttFiber44Prefix63 = ttFiber44Prefix62 ++ [ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 63) []
    (chainClosureStep ttWord ttFiber44Prefix62 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 31) hparentBefore ttFiber44ReverseSingleStep63

theorem ttFiber44State63_in_pass1_full :
    ttFiber44StateAt 63 ∈ chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber44Prefix63 ([ttFiber44StateAt 0]))
    (ttFiber44StateAt 63) ttFiber44State63_in_pass1_prefix63

theorem ttFiber44State16_in_pass2_prefix16 :
    ttFiber44StateAt 16 ∈ chainClosureStep ttWord ttFiber44Prefix16 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  have hparentBefore : ttFiber44StateAt 20 ∈
      chainClosureStep ttWord ttFiber44Prefix15 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix15
      (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 20) ttFiber44State20_in_pass1_full
  rw [show ttFiber44Prefix16 = ttFiber44Prefix15 ++ [ttFiber44StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 16) []
    (chainClosureStep ttWord ttFiber44Prefix15 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 20) hparentBefore ttFiber44ReverseSingleStep16

theorem ttFiber44State16_in_pass2_full :
    ttFiber44StateAt 16 ∈ chainClosureStep ttWord ttFiber44DirectStates (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix16 ++ [ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 17, ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix16 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 16) ttFiber44State16_in_pass2_prefix16

theorem ttFiber44State17_in_pass2_prefix17 :
    ttFiber44StateAt 17 ∈ chainClosureStep ttWord ttFiber44Prefix17 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  have hparentBefore : ttFiber44StateAt 21 ∈
      chainClosureStep ttWord ttFiber44Prefix16 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix16
      (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 21) ttFiber44State21_in_pass1_full
  rw [show ttFiber44Prefix17 = ttFiber44Prefix16 ++ [ttFiber44StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 17) []
    (chainClosureStep ttWord ttFiber44Prefix16 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 21) hparentBefore ttFiber44ReverseSingleStep17

theorem ttFiber44State17_in_pass2_full :
    ttFiber44StateAt 17 ∈ chainClosureStep ttWord ttFiber44DirectStates (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix17 ++ [ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 18, ttFiber44StateAt 19, ttFiber44StateAt 20, ttFiber44StateAt 21, ttFiber44StateAt 22, ttFiber44StateAt 23, ttFiber44StateAt 24, ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix17 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 17) ttFiber44State17_in_pass2_prefix17

theorem ttFiber44State24_in_pass2_prefix24 :
    ttFiber44StateAt 24 ∈ chainClosureStep ttWord ttFiber44Prefix24 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  have hparentBefore : ttFiber44StateAt 28 ∈
      chainClosureStep ttWord ttFiber44Prefix23 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix23
      (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 28) ttFiber44State28_in_pass1_full
  rw [show ttFiber44Prefix24 = ttFiber44Prefix23 ++ [ttFiber44StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 24) []
    (chainClosureStep ttWord ttFiber44Prefix23 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 28) hparentBefore ttFiber44ReverseSingleStep24

theorem ttFiber44State24_in_pass2_full :
    ttFiber44StateAt 24 ∈ chainClosureStep ttWord ttFiber44DirectStates (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix24 ++ [ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 25, ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix24 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 24) ttFiber44State24_in_pass2_prefix24

theorem ttFiber44State25_in_pass2_prefix25 :
    ttFiber44StateAt 25 ∈ chainClosureStep ttWord ttFiber44Prefix25 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  have hparentBefore : ttFiber44StateAt 29 ∈
      chainClosureStep ttWord ttFiber44Prefix24 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber44Prefix24
      (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0]))
      (ttFiber44StateAt 29) ttFiber44State29_in_pass1_full
  rw [show ttFiber44Prefix25 = ttFiber44Prefix24 ++ [ttFiber44StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber44StateAt 25) []
    (chainClosureStep ttWord ttFiber44Prefix24 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 29) hparentBefore ttFiber44ReverseSingleStep25

theorem ttFiber44State25_in_pass2_full :
    ttFiber44StateAt 25 ∈ chainClosureStep ttWord ttFiber44DirectStates (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])) := by
  rw [show ttFiber44DirectStates = ttFiber44Prefix25 ++ [ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber44StateAt 26, ttFiber44StateAt 27, ttFiber44StateAt 28, ttFiber44StateAt 29, ttFiber44StateAt 30, ttFiber44StateAt 31, ttFiber44StateAt 32, ttFiber44StateAt 33, ttFiber44StateAt 34, ttFiber44StateAt 35, ttFiber44StateAt 36, ttFiber44StateAt 37, ttFiber44StateAt 38, ttFiber44StateAt 39, ttFiber44StateAt 40, ttFiber44StateAt 41, ttFiber44StateAt 42, ttFiber44StateAt 43, ttFiber44StateAt 44, ttFiber44StateAt 45, ttFiber44StateAt 46, ttFiber44StateAt 47, ttFiber44StateAt 48, ttFiber44StateAt 49, ttFiber44StateAt 50, ttFiber44StateAt 51, ttFiber44StateAt 52, ttFiber44StateAt 53, ttFiber44StateAt 54, ttFiber44StateAt 55, ttFiber44StateAt 56, ttFiber44StateAt 57, ttFiber44StateAt 58, ttFiber44StateAt 59, ttFiber44StateAt 60, ttFiber44StateAt 61, ttFiber44StateAt 62, ttFiber44StateAt 63]
    (chainClosureStep ttWord ttFiber44Prefix25 (chainClosureStep ttWord ttFiber44DirectStates ([ttFiber44StateAt 0])))
    (ttFiber44StateAt 25) ttFiber44State25_in_pass2_prefix25

theorem ttFiber44State0_in_close :
    ttFiber44StateAt 0 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber44DirectStates ttFiber44DirectStates.length
    [ttFiber44StateAt 0] (ttFiber44StateAt 0) (by simp)

theorem ttFiber44State1_in_close :
    ttFiber44StateAt 1 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 1 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 1) ttFiber44State1_in_pass1_full

theorem ttFiber44State2_in_close :
    ttFiber44StateAt 2 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 2 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 2) ttFiber44State2_in_pass1_full

theorem ttFiber44State3_in_close :
    ttFiber44StateAt 3 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 3 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 3) ttFiber44State3_in_pass1_full

theorem ttFiber44State4_in_close :
    ttFiber44StateAt 4 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 4 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 4) ttFiber44State4_in_pass1_full

theorem ttFiber44State5_in_close :
    ttFiber44StateAt 5 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 5 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 5) ttFiber44State5_in_pass1_full

theorem ttFiber44State6_in_close :
    ttFiber44StateAt 6 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 6 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 6) ttFiber44State6_in_pass1_full

theorem ttFiber44State7_in_close :
    ttFiber44StateAt 7 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 7 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 7) ttFiber44State7_in_pass1_full

theorem ttFiber44State8_in_close :
    ttFiber44StateAt 8 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 8 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 8) ttFiber44State8_in_pass1_full

theorem ttFiber44State9_in_close :
    ttFiber44StateAt 9 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 9 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 9) ttFiber44State9_in_pass1_full

theorem ttFiber44State10_in_close :
    ttFiber44StateAt 10 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 10 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 10) ttFiber44State10_in_pass1_full

theorem ttFiber44State11_in_close :
    ttFiber44StateAt 11 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 11 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 11) ttFiber44State11_in_pass1_full

theorem ttFiber44State12_in_close :
    ttFiber44StateAt 12 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 12 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 12) ttFiber44State12_in_pass1_full

theorem ttFiber44State13_in_close :
    ttFiber44StateAt 13 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 13 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 13) ttFiber44State13_in_pass1_full

theorem ttFiber44State14_in_close :
    ttFiber44StateAt 14 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 14 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 14) ttFiber44State14_in_pass1_full

theorem ttFiber44State15_in_close :
    ttFiber44StateAt 15 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 15 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 15) ttFiber44State15_in_pass1_full

theorem ttFiber44State16_in_close :
    ttFiber44StateAt 16 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 16 ∈ closeChainFiber ttWord ttFiber44DirectStates (62 + 2)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber44DirectStates 62
    [ttFiber44StateAt 0] (ttFiber44StateAt 16) ttFiber44FirstPassGrows
    ttFiber44State16_in_pass2_full

theorem ttFiber44State17_in_close :
    ttFiber44StateAt 17 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 17 ∈ closeChainFiber ttWord ttFiber44DirectStates (62 + 2)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber44DirectStates 62
    [ttFiber44StateAt 0] (ttFiber44StateAt 17) ttFiber44FirstPassGrows
    ttFiber44State17_in_pass2_full

theorem ttFiber44State18_in_close :
    ttFiber44StateAt 18 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 18 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 18) ttFiber44State18_in_pass1_full

theorem ttFiber44State19_in_close :
    ttFiber44StateAt 19 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 19 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 19) ttFiber44State19_in_pass1_full

theorem ttFiber44State20_in_close :
    ttFiber44StateAt 20 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 20 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 20) ttFiber44State20_in_pass1_full

theorem ttFiber44State21_in_close :
    ttFiber44StateAt 21 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 21 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 21) ttFiber44State21_in_pass1_full

theorem ttFiber44State22_in_close :
    ttFiber44StateAt 22 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 22 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 22) ttFiber44State22_in_pass1_full

theorem ttFiber44State23_in_close :
    ttFiber44StateAt 23 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 23 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 23) ttFiber44State23_in_pass1_full

theorem ttFiber44State24_in_close :
    ttFiber44StateAt 24 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 24 ∈ closeChainFiber ttWord ttFiber44DirectStates (62 + 2)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber44DirectStates 62
    [ttFiber44StateAt 0] (ttFiber44StateAt 24) ttFiber44FirstPassGrows
    ttFiber44State24_in_pass2_full

theorem ttFiber44State25_in_close :
    ttFiber44StateAt 25 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 25 ∈ closeChainFiber ttWord ttFiber44DirectStates (62 + 2)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber44DirectStates 62
    [ttFiber44StateAt 0] (ttFiber44StateAt 25) ttFiber44FirstPassGrows
    ttFiber44State25_in_pass2_full

theorem ttFiber44State26_in_close :
    ttFiber44StateAt 26 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 26 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 26) ttFiber44State26_in_pass1_full

theorem ttFiber44State27_in_close :
    ttFiber44StateAt 27 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 27 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 27) ttFiber44State27_in_pass1_full

theorem ttFiber44State28_in_close :
    ttFiber44StateAt 28 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 28 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 28) ttFiber44State28_in_pass1_full

theorem ttFiber44State29_in_close :
    ttFiber44StateAt 29 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 29 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 29) ttFiber44State29_in_pass1_full

theorem ttFiber44State30_in_close :
    ttFiber44StateAt 30 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 30 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 30) ttFiber44State30_in_pass1_full

theorem ttFiber44State31_in_close :
    ttFiber44StateAt 31 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 31 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 31) ttFiber44State31_in_pass1_full

theorem ttFiber44State32_in_close :
    ttFiber44StateAt 32 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 32 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 32) ttFiber44State32_in_pass1_full

theorem ttFiber44State33_in_close :
    ttFiber44StateAt 33 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 33 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 33) ttFiber44State33_in_pass1_full

theorem ttFiber44State34_in_close :
    ttFiber44StateAt 34 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 34 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 34) ttFiber44State34_in_pass1_full

theorem ttFiber44State35_in_close :
    ttFiber44StateAt 35 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 35 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 35) ttFiber44State35_in_pass1_full

theorem ttFiber44State36_in_close :
    ttFiber44StateAt 36 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 36 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 36) ttFiber44State36_in_pass1_full

theorem ttFiber44State37_in_close :
    ttFiber44StateAt 37 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 37 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 37) ttFiber44State37_in_pass1_full

theorem ttFiber44State38_in_close :
    ttFiber44StateAt 38 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 38 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 38) ttFiber44State38_in_pass1_full

theorem ttFiber44State39_in_close :
    ttFiber44StateAt 39 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 39 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 39) ttFiber44State39_in_pass1_full

theorem ttFiber44State40_in_close :
    ttFiber44StateAt 40 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 40 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 40) ttFiber44State40_in_pass1_full

theorem ttFiber44State41_in_close :
    ttFiber44StateAt 41 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 41 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 41) ttFiber44State41_in_pass1_full

theorem ttFiber44State42_in_close :
    ttFiber44StateAt 42 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 42 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 42) ttFiber44State42_in_pass1_full

theorem ttFiber44State43_in_close :
    ttFiber44StateAt 43 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 43 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 43) ttFiber44State43_in_pass1_full

theorem ttFiber44State44_in_close :
    ttFiber44StateAt 44 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 44 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 44) ttFiber44State44_in_pass1_full

theorem ttFiber44State45_in_close :
    ttFiber44StateAt 45 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 45 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 45) ttFiber44State45_in_pass1_full

theorem ttFiber44State46_in_close :
    ttFiber44StateAt 46 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 46 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 46) ttFiber44State46_in_pass1_full

theorem ttFiber44State47_in_close :
    ttFiber44StateAt 47 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 47 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 47) ttFiber44State47_in_pass1_full

theorem ttFiber44State48_in_close :
    ttFiber44StateAt 48 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 48 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 48) ttFiber44State48_in_pass1_full

theorem ttFiber44State49_in_close :
    ttFiber44StateAt 49 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 49 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 49) ttFiber44State49_in_pass1_full

theorem ttFiber44State50_in_close :
    ttFiber44StateAt 50 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 50 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 50) ttFiber44State50_in_pass1_full

theorem ttFiber44State51_in_close :
    ttFiber44StateAt 51 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 51 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 51) ttFiber44State51_in_pass1_full

theorem ttFiber44State52_in_close :
    ttFiber44StateAt 52 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 52 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 52) ttFiber44State52_in_pass1_full

theorem ttFiber44State53_in_close :
    ttFiber44StateAt 53 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 53 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 53) ttFiber44State53_in_pass1_full

theorem ttFiber44State54_in_close :
    ttFiber44StateAt 54 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 54 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 54) ttFiber44State54_in_pass1_full

theorem ttFiber44State55_in_close :
    ttFiber44StateAt 55 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 55 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 55) ttFiber44State55_in_pass1_full

theorem ttFiber44State56_in_close :
    ttFiber44StateAt 56 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 56 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 56) ttFiber44State56_in_pass1_full

theorem ttFiber44State57_in_close :
    ttFiber44StateAt 57 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 57 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 57) ttFiber44State57_in_pass1_full

theorem ttFiber44State58_in_close :
    ttFiber44StateAt 58 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 58 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 58) ttFiber44State58_in_pass1_full

theorem ttFiber44State59_in_close :
    ttFiber44StateAt 59 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 59 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 59) ttFiber44State59_in_pass1_full

theorem ttFiber44State60_in_close :
    ttFiber44StateAt 60 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 60 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 60) ttFiber44State60_in_pass1_full

theorem ttFiber44State61_in_close :
    ttFiber44StateAt 61 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 61 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 61) ttFiber44State61_in_pass1_full

theorem ttFiber44State62_in_close :
    ttFiber44StateAt 62 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 62 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 62) ttFiber44State62_in_pass1_full

theorem ttFiber44State63_in_close :
    ttFiber44StateAt 63 ∈
      closeChainFiber ttWord ttFiber44DirectStates ttFiber44DirectStates.length
        [ttFiber44StateAt 0] := by
  change ttFiber44StateAt 63 ∈ closeChainFiber ttWord ttFiber44DirectStates (63 + 1)
    [ttFiber44StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber44DirectStates 63
    [ttFiber44StateAt 0] (ttFiber44StateAt 63) ttFiber44State63_in_pass1_full

theorem ttFiber44DirectConnected :
    chainFiberConnected ttWord ttFiber44DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber44DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber44State0_in_close
  · subst state
    exact ttFiber44State1_in_close
  · subst state
    exact ttFiber44State2_in_close
  · subst state
    exact ttFiber44State3_in_close
  · subst state
    exact ttFiber44State4_in_close
  · subst state
    exact ttFiber44State5_in_close
  · subst state
    exact ttFiber44State6_in_close
  · subst state
    exact ttFiber44State7_in_close
  · subst state
    exact ttFiber44State8_in_close
  · subst state
    exact ttFiber44State9_in_close
  · subst state
    exact ttFiber44State10_in_close
  · subst state
    exact ttFiber44State11_in_close
  · subst state
    exact ttFiber44State12_in_close
  · subst state
    exact ttFiber44State13_in_close
  · subst state
    exact ttFiber44State14_in_close
  · subst state
    exact ttFiber44State15_in_close
  · subst state
    exact ttFiber44State16_in_close
  · subst state
    exact ttFiber44State17_in_close
  · subst state
    exact ttFiber44State18_in_close
  · subst state
    exact ttFiber44State19_in_close
  · subst state
    exact ttFiber44State20_in_close
  · subst state
    exact ttFiber44State21_in_close
  · subst state
    exact ttFiber44State22_in_close
  · subst state
    exact ttFiber44State23_in_close
  · subst state
    exact ttFiber44State24_in_close
  · subst state
    exact ttFiber44State25_in_close
  · subst state
    exact ttFiber44State26_in_close
  · subst state
    exact ttFiber44State27_in_close
  · subst state
    exact ttFiber44State28_in_close
  · subst state
    exact ttFiber44State29_in_close
  · subst state
    exact ttFiber44State30_in_close
  · subst state
    exact ttFiber44State31_in_close
  · subst state
    exact ttFiber44State32_in_close
  · subst state
    exact ttFiber44State33_in_close
  · subst state
    exact ttFiber44State34_in_close
  · subst state
    exact ttFiber44State35_in_close
  · subst state
    exact ttFiber44State36_in_close
  · subst state
    exact ttFiber44State37_in_close
  · subst state
    exact ttFiber44State38_in_close
  · subst state
    exact ttFiber44State39_in_close
  · subst state
    exact ttFiber44State40_in_close
  · subst state
    exact ttFiber44State41_in_close
  · subst state
    exact ttFiber44State42_in_close
  · subst state
    exact ttFiber44State43_in_close
  · subst state
    exact ttFiber44State44_in_close
  · subst state
    exact ttFiber44State45_in_close
  · subst state
    exact ttFiber44State46_in_close
  · subst state
    exact ttFiber44State47_in_close
  · subst state
    exact ttFiber44State48_in_close
  · subst state
    exact ttFiber44State49_in_close
  · subst state
    exact ttFiber44State50_in_close
  · subst state
    exact ttFiber44State51_in_close
  · subst state
    exact ttFiber44State52_in_close
  · subst state
    exact ttFiber44State53_in_close
  · subst state
    exact ttFiber44State54_in_close
  · subst state
    exact ttFiber44State55_in_close
  · subst state
    exact ttFiber44State56_in_close
  · subst state
    exact ttFiber44State57_in_close
  · subst state
    exact ttFiber44State58_in_close
  · subst state
    exact ttFiber44State59_in_close
  · subst state
    exact ttFiber44State60_in_close
  · subst state
    exact ttFiber44State61_in_close
  · subst state
    exact ttFiber44State62_in_close
  · subst state
    exact ttFiber44State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
