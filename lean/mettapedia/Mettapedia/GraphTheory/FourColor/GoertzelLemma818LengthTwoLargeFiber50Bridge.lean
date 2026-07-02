import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber50

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber50StateAt (i : Nat) : List TauState :=
  directStates (ttFiber50RowAt i).sourceLeft (ttFiber50RowAt i).sourceRight

def ttFiber50DirectStates : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]

def ttFiber50Prefix0 : List (List TauState) :=
  [ttFiber50StateAt 0]

def ttFiber50Prefix1 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1]

def ttFiber50Prefix2 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2]

def ttFiber50Prefix3 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3]

def ttFiber50Prefix4 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4]

def ttFiber50Prefix5 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5]

def ttFiber50Prefix6 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6]

def ttFiber50Prefix7 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7]

def ttFiber50Prefix8 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8]

def ttFiber50Prefix9 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9]

def ttFiber50Prefix10 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10]

def ttFiber50Prefix11 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11]

def ttFiber50Prefix12 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12]

def ttFiber50Prefix13 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13]

def ttFiber50Prefix14 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14]

def ttFiber50Prefix15 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15]

def ttFiber50Prefix16 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16]

def ttFiber50Prefix17 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17]

def ttFiber50Prefix18 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18]

def ttFiber50Prefix19 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19]

def ttFiber50Prefix20 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20]

def ttFiber50Prefix21 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21]

def ttFiber50Prefix22 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22]

def ttFiber50Prefix23 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23]

def ttFiber50Prefix24 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24]

def ttFiber50Prefix25 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25]

def ttFiber50Prefix26 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26]

def ttFiber50Prefix27 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27]

def ttFiber50Prefix28 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28]

def ttFiber50Prefix29 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29]

def ttFiber50Prefix30 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30]

def ttFiber50Prefix31 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31]

def ttFiber50Prefix32 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32]

def ttFiber50Prefix33 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33]

def ttFiber50Prefix34 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34]

def ttFiber50Prefix35 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35]

def ttFiber50Prefix36 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36]

def ttFiber50Prefix37 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37]

def ttFiber50Prefix38 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38]

def ttFiber50Prefix39 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39]

def ttFiber50Prefix40 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40]

def ttFiber50Prefix41 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41]

def ttFiber50Prefix42 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42]

def ttFiber50Prefix43 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43]

def ttFiber50Prefix44 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44]

def ttFiber50Prefix45 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45]

def ttFiber50Prefix46 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46]

def ttFiber50Prefix47 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47]

def ttFiber50Prefix48 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48]

def ttFiber50Prefix49 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49]

def ttFiber50Prefix50 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50]

def ttFiber50Prefix51 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51]

def ttFiber50Prefix52 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52]

def ttFiber50Prefix53 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53]

def ttFiber50Prefix54 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54]

def ttFiber50Prefix55 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55]

def ttFiber50Prefix56 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56]

def ttFiber50Prefix57 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57]

def ttFiber50Prefix58 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58]

def ttFiber50Prefix59 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59]

def ttFiber50Prefix60 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60]

def ttFiber50Prefix61 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61]

def ttFiber50Prefix62 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62]

def ttFiber50Prefix63 : List (List TauState) :=
  [ttFiber50StateAt 0, ttFiber50StateAt 1, ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]

theorem ttFiber50ReverseRow_1_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk0] at h
  exact h.2

theorem ttFiber50ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 1)
      (ttFiber50RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 1) (by decide) ttFiber50ReverseRow_1_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_2_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk1] at h
  exact h.1

theorem ttFiber50ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 2)
      (ttFiber50RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 2) (by decide) ttFiber50ReverseRow_2_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_3_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk1] at h
  exact h.2

theorem ttFiber50ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 3)
      (ttFiber50RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 3) (by decide) ttFiber50ReverseRow_3_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_4_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk2] at h
  exact h.1

theorem ttFiber50ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 4)
      (ttFiber50RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 4) (by decide) ttFiber50ReverseRow_4_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_5_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk2] at h
  exact h.2

theorem ttFiber50ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 5)
      (ttFiber50RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 5) (by decide) ttFiber50ReverseRow_5_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_6_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk3] at h
  exact h.1

theorem ttFiber50ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 6)
      (ttFiber50RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 6) (by decide) ttFiber50ReverseRow_6_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_7_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk3] at h
  exact h.2

theorem ttFiber50ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 7)
      (ttFiber50RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 7) (by decide) ttFiber50ReverseRow_7_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_8_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk4] at h
  exact h.1

theorem ttFiber50ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 8)
      (ttFiber50RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 8) (by decide) ttFiber50ReverseRow_8_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_9_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk4] at h
  exact h.2

theorem ttFiber50ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 9)
      (ttFiber50RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 9) (by decide) ttFiber50ReverseRow_9_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_10_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk5] at h
  exact h.1

theorem ttFiber50ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 10)
      (ttFiber50RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 10) (by decide) ttFiber50ReverseRow_10_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_11_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk5] at h
  exact h.2

theorem ttFiber50ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 11)
      (ttFiber50RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 11) (by decide) ttFiber50ReverseRow_11_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_12_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk6] at h
  exact h.1

theorem ttFiber50ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 12)
      (ttFiber50RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 12) (by decide) ttFiber50ReverseRow_12_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_13_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk6] at h
  exact h.2

theorem ttFiber50ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 13)
      (ttFiber50RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 13) (by decide) ttFiber50ReverseRow_13_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_14_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk7] at h
  exact h.1

theorem ttFiber50ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 6) (ttFiber50StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 6) (ttFiber50StateAt 14)
      (ttFiber50RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 14) (by decide) ttFiber50ReverseRow_14_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_15_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk7] at h
  exact h.2

theorem ttFiber50ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 7) (ttFiber50StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 7) (ttFiber50StateAt 15)
      (ttFiber50RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 15) (by decide) ttFiber50ReverseRow_15_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_16_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk8] at h
  exact h.1

theorem ttFiber50ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 20) (ttFiber50StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 20) (ttFiber50StateAt 16)
      (ttFiber50RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 16) (by decide) ttFiber50ReverseRow_16_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_17_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk8] at h
  exact h.2

theorem ttFiber50ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 21) (ttFiber50StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 21) (ttFiber50StateAt 17)
      (ttFiber50RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 17) (by decide) ttFiber50ReverseRow_17_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_18_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk9] at h
  exact h.1

theorem ttFiber50ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 12) (ttFiber50StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 12) (ttFiber50StateAt 18)
      (ttFiber50RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 18) (by decide) ttFiber50ReverseRow_18_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_19_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk9] at h
  exact h.2

theorem ttFiber50ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 13) (ttFiber50StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 13) (ttFiber50StateAt 19)
      (ttFiber50RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 19) (by decide) ttFiber50ReverseRow_19_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_20_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk10] at h
  exact h.1

theorem ttFiber50ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 8) (ttFiber50StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 8) (ttFiber50StateAt 20)
      (ttFiber50RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 20) (by decide) ttFiber50ReverseRow_20_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_21_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk10] at h
  exact h.2

theorem ttFiber50ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 9) (ttFiber50StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 9) (ttFiber50StateAt 21)
      (ttFiber50RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 21) (by decide) ttFiber50ReverseRow_21_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_22_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk11] at h
  exact h.1

theorem ttFiber50ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 10) (ttFiber50StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 10) (ttFiber50StateAt 22)
      (ttFiber50RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 22) (by decide) ttFiber50ReverseRow_22_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_23_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk11] at h
  exact h.2

theorem ttFiber50ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 11) (ttFiber50StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 11) (ttFiber50StateAt 23)
      (ttFiber50RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 23) (by decide) ttFiber50ReverseRow_23_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_24_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk12] at h
  exact h.1

theorem ttFiber50ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 28) (ttFiber50StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 28) (ttFiber50StateAt 24)
      (ttFiber50RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 24) (by decide) ttFiber50ReverseRow_24_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_25_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk12] at h
  exact h.2

theorem ttFiber50ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 29) (ttFiber50StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 29) (ttFiber50StateAt 25)
      (ttFiber50RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 25) (by decide) ttFiber50ReverseRow_25_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_26_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk13] at h
  exact h.1

theorem ttFiber50ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 26)
      (ttFiber50RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 26) (by decide) ttFiber50ReverseRow_26_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_27_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk13] at h
  exact h.2

theorem ttFiber50ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 27)
      (ttFiber50RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 27) (by decide) ttFiber50ReverseRow_27_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_28_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk14] at h
  exact h.1

theorem ttFiber50ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 28)
      (ttFiber50RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 28) (by decide) ttFiber50ReverseRow_28_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_29_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk14] at h
  exact h.2

theorem ttFiber50ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 29)
      (ttFiber50RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 29) (by decide) ttFiber50ReverseRow_29_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_30_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk15] at h
  exact h.1

theorem ttFiber50ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 30)
      (ttFiber50RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 30) (by decide) ttFiber50ReverseRow_30_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_31_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk15] at h
  exact h.2

theorem ttFiber50ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 31)
      (ttFiber50RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 31) (by decide) ttFiber50ReverseRow_31_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_32_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk16] at h
  exact h.1

theorem ttFiber50ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 0) (ttFiber50StateAt 32)
      (ttFiber50RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 32) (by decide) ttFiber50ReverseRow_32_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_33_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk16] at h
  exact h.2

theorem ttFiber50ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 1) (ttFiber50StateAt 33)
      (ttFiber50RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 33) (by decide) ttFiber50ReverseRow_33_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_34_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk17] at h
  exact h.1

theorem ttFiber50ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 2) (ttFiber50StateAt 34)
      (ttFiber50RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 34) (by decide) ttFiber50ReverseRow_34_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_35_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk17] at h
  exact h.2

theorem ttFiber50ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 3) (ttFiber50StateAt 35)
      (ttFiber50RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 35) (by decide) ttFiber50ReverseRow_35_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_36_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk18] at h
  exact h.1

theorem ttFiber50ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 4) (ttFiber50StateAt 36)
      (ttFiber50RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 36) (by decide) ttFiber50ReverseRow_36_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_37_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk18] at h
  exact h.2

theorem ttFiber50ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 5) (ttFiber50StateAt 37)
      (ttFiber50RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 37) (by decide) ttFiber50ReverseRow_37_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_38_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk19] at h
  exact h.1

theorem ttFiber50ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 6) (ttFiber50StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 6) (ttFiber50StateAt 38)
      (ttFiber50RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 38) (by decide) ttFiber50ReverseRow_38_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_39_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk19] at h
  exact h.2

theorem ttFiber50ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 7) (ttFiber50StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 7) (ttFiber50StateAt 39)
      (ttFiber50RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 39) (by decide) ttFiber50ReverseRow_39_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_40_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk20] at h
  exact h.1

theorem ttFiber50ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 8) (ttFiber50StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 8) (ttFiber50StateAt 40)
      (ttFiber50RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 40) (by decide) ttFiber50ReverseRow_40_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_41_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk20] at h
  exact h.2

theorem ttFiber50ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 9) (ttFiber50StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 9) (ttFiber50StateAt 41)
      (ttFiber50RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 41) (by decide) ttFiber50ReverseRow_41_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_42_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk21] at h
  exact h.1

theorem ttFiber50ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 10) (ttFiber50StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 10) (ttFiber50StateAt 42)
      (ttFiber50RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 42) (by decide) ttFiber50ReverseRow_42_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_43_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk21] at h
  exact h.2

theorem ttFiber50ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 11) (ttFiber50StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 11) (ttFiber50StateAt 43)
      (ttFiber50RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 43) (by decide) ttFiber50ReverseRow_43_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_44_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk22] at h
  exact h.1

theorem ttFiber50ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 12) (ttFiber50StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 12) (ttFiber50StateAt 44)
      (ttFiber50RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 44) (by decide) ttFiber50ReverseRow_44_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_45_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk22] at h
  exact h.2

theorem ttFiber50ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 13) (ttFiber50StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 13) (ttFiber50StateAt 45)
      (ttFiber50RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 45) (by decide) ttFiber50ReverseRow_45_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_46_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk23] at h
  exact h.1

theorem ttFiber50ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 14) (ttFiber50StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 14) (ttFiber50StateAt 46)
      (ttFiber50RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 46) (by decide) ttFiber50ReverseRow_46_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_47_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk23] at h
  exact h.2

theorem ttFiber50ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 15) (ttFiber50StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 15) (ttFiber50StateAt 47)
      (ttFiber50RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 47) (by decide) ttFiber50ReverseRow_47_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_48_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk24] at h
  exact h.1

theorem ttFiber50ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 32) (ttFiber50StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 32) (ttFiber50StateAt 48)
      (ttFiber50RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 48) (by decide) ttFiber50ReverseRow_48_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_49_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk24] at h
  exact h.2

theorem ttFiber50ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 33) (ttFiber50StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 33) (ttFiber50StateAt 49)
      (ttFiber50RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 49) (by decide) ttFiber50ReverseRow_49_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_50_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk25] at h
  exact h.1

theorem ttFiber50ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 48) (ttFiber50StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 48) (ttFiber50StateAt 50)
      (ttFiber50RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 50) (by decide) ttFiber50ReverseRow_50_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_51_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk25] at h
  exact h.2

theorem ttFiber50ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 35) (ttFiber50StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 35) (ttFiber50StateAt 51)
      (ttFiber50RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 51) (by decide) ttFiber50ReverseRow_51_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_52_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk26] at h
  exact h.1

theorem ttFiber50ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 36) (ttFiber50StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 36) (ttFiber50StateAt 52)
      (ttFiber50RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 52) (by decide) ttFiber50ReverseRow_52_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_53_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk26] at h
  exact h.2

theorem ttFiber50ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 37) (ttFiber50StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 37) (ttFiber50StateAt 53)
      (ttFiber50RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 53) (by decide) ttFiber50ReverseRow_53_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_54_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk27] at h
  exact h.1

theorem ttFiber50ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 49) (ttFiber50StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 49) (ttFiber50StateAt 54)
      (ttFiber50RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 54) (by decide) ttFiber50ReverseRow_54_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_55_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk27] at h
  exact h.2

theorem ttFiber50ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 48) (ttFiber50StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 48) (ttFiber50StateAt 55)
      (ttFiber50RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 55) (by decide) ttFiber50ReverseRow_55_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_56_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk28] at h
  exact h.1

theorem ttFiber50ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 40) (ttFiber50StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 40) (ttFiber50StateAt 56)
      (ttFiber50RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 56) (by decide) ttFiber50ReverseRow_56_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_57_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk28] at h
  exact h.2

theorem ttFiber50ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 41) (ttFiber50StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 41) (ttFiber50StateAt 57)
      (ttFiber50RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 57) (by decide) ttFiber50ReverseRow_57_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_58_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk29] at h
  exact h.1

theorem ttFiber50ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 26) (ttFiber50StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 26) (ttFiber50StateAt 58)
      (ttFiber50RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 58) (by decide) ttFiber50ReverseRow_58_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_59_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk29] at h
  exact h.2

theorem ttFiber50ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 27) (ttFiber50StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 27) (ttFiber50StateAt 59)
      (ttFiber50RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 59) (by decide) ttFiber50ReverseRow_59_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_60_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk30] at h
  exact h.1

theorem ttFiber50ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 28) (ttFiber50StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 28) (ttFiber50StateAt 60)
      (ttFiber50RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 60) (by decide) ttFiber50ReverseRow_60_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_61_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk30] at h
  exact h.2

theorem ttFiber50ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 29) (ttFiber50StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 29) (ttFiber50StateAt 61)
      (ttFiber50RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 61) (by decide) ttFiber50ReverseRow_61_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_62_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk31] at h
  exact h.1

theorem ttFiber50ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 60) (ttFiber50StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 60) (ttFiber50StateAt 62)
      (ttFiber50RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 62) (by decide) ttFiber50ReverseRow_62_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50ReverseRow_63_ok' :
    directRowReverseValid ttFiber50Key ttFiber50Expected (ttFiber50RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber50Chunk31] at h
  exact h.2

theorem ttFiber50ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber50StateAt 31) (ttFiber50StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber50StateAt 31) (ttFiber50StateAt 63)
      (ttFiber50RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber50Key ttFiber50Expected
      (ttFiber50RowAt 63) (by decide) ttFiber50ReverseRow_63_ok'
    simpa [ttFiber50StateAt, ttFiber50RowAt, ttFiber50Rows, listGetD, directRow] using h

theorem ttFiber50FirstPassGrows :
    ((chainClosureStep ttWord ttFiber50DirectStates [ttFiber50StateAt 0]).length ==
      [ttFiber50StateAt 0].length) = false := by
  have hroot : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50DirectStates [ttFiber50StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber50DirectStates [ttFiber50StateAt 0]
      (ttFiber50StateAt 0) (by simp)
  have hnew : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50DirectStates [ttFiber50StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber50DirectStates [ttFiber50StateAt 0]
      (ttFiber50StateAt 0) (ttFiber50StateAt 1) (by decide) (by simp)
      ttFiber50ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber50DirectStates [ttFiber50StateAt 0])
    (ttFiber50StateAt 0) (ttFiber50StateAt 1) hroot hnew (by decide)

theorem ttFiber50State0_in_pass0_full :
    ttFiber50StateAt 0 ∈ [ttFiber50StateAt 0] := by
  simp

theorem ttFiber50State0_in_pass1_full :
    ttFiber50StateAt 0 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber50DirectStates
    ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full

theorem ttFiber50State1_in_pass1_prefix1 :
    ttFiber50StateAt 1 ∈ chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix0 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix0
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix1 = ttFiber50Prefix0 ++ [ttFiber50StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 1) []
    (chainClosureStep ttWord ttFiber50Prefix0 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep1

theorem ttFiber50State1_in_pass1_full :
    ttFiber50StateAt 1 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix1 ++ [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1

theorem ttFiber50State2_in_pass1_prefix2 :
    ttFiber50StateAt 2 ∈ chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix1 = ttFiber50Prefix1 ++ [] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord []
      (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1
  rw [show ttFiber50Prefix2 = ttFiber50Prefix1 ++ [ttFiber50StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 2) []
    (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) hparentBefore ttFiber50ReverseSingleStep2

theorem ttFiber50State2_in_pass1_full :
    ttFiber50StateAt 2 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix2 ++ [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 2) ttFiber50State2_in_pass1_prefix2

theorem ttFiber50State3_in_pass1_prefix3 :
    ttFiber50StateAt 3 ∈ chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix2
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix3 = ttFiber50Prefix2 ++ [ttFiber50StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 3) []
    (chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep3

theorem ttFiber50State3_in_pass1_full :
    ttFiber50StateAt 3 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix3 ++ [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 3) ttFiber50State3_in_pass1_prefix3

theorem ttFiber50State4_in_pass1_prefix4 :
    ttFiber50StateAt 4 ∈ chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix3
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix4 = ttFiber50Prefix3 ++ [ttFiber50StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 4) []
    (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep4

theorem ttFiber50State4_in_pass1_full :
    ttFiber50StateAt 4 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix4 ++ [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 4) ttFiber50State4_in_pass1_prefix4

theorem ttFiber50State5_in_pass1_prefix5 :
    ttFiber50StateAt 5 ∈ chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix4 = ttFiber50Prefix1 ++ [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4]
      (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1
  rw [show ttFiber50Prefix5 = ttFiber50Prefix4 ++ [ttFiber50StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 5) []
    (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) hparentBefore ttFiber50ReverseSingleStep5

theorem ttFiber50State5_in_pass1_full :
    ttFiber50StateAt 5 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix5 ++ [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 5) ttFiber50State5_in_pass1_prefix5

theorem ttFiber50State6_in_pass1_prefix6 :
    ttFiber50StateAt 6 ∈ chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 4 ∈
      chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix5 = ttFiber50Prefix4 ++ [ttFiber50StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 5]
      (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 4) ttFiber50State4_in_pass1_prefix4
  rw [show ttFiber50Prefix6 = ttFiber50Prefix5 ++ [ttFiber50StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 6) []
    (chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 4) hparentBefore ttFiber50ReverseSingleStep6

theorem ttFiber50State6_in_pass1_full :
    ttFiber50StateAt 6 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix6 ++ [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 6) ttFiber50State6_in_pass1_prefix6

theorem ttFiber50State7_in_pass1_prefix7 :
    ttFiber50StateAt 7 ∈ chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 3 ∈
      chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix6 = ttFiber50Prefix3 ++ [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6]
      (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 3) ttFiber50State3_in_pass1_prefix3
  rw [show ttFiber50Prefix7 = ttFiber50Prefix6 ++ [ttFiber50StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 7) []
    (chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 3) hparentBefore ttFiber50ReverseSingleStep7

theorem ttFiber50State7_in_pass1_full :
    ttFiber50StateAt 7 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix7 ++ [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 7) ttFiber50State7_in_pass1_prefix7

theorem ttFiber50State8_in_pass1_prefix8 :
    ttFiber50StateAt 8 ∈ chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix7
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix8 = ttFiber50Prefix7 ++ [ttFiber50StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 8) []
    (chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep8

theorem ttFiber50State8_in_pass1_full :
    ttFiber50StateAt 8 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix8 ++ [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 8) ttFiber50State8_in_pass1_prefix8

theorem ttFiber50State9_in_pass1_prefix9 :
    ttFiber50StateAt 9 ∈ chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix8 = ttFiber50Prefix1 ++ [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8]
      (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1
  rw [show ttFiber50Prefix9 = ttFiber50Prefix8 ++ [ttFiber50StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 9) []
    (chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) hparentBefore ttFiber50ReverseSingleStep9

theorem ttFiber50State9_in_pass1_full :
    ttFiber50StateAt 9 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix9 ++ [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 9) ttFiber50State9_in_pass1_prefix9

theorem ttFiber50State10_in_pass1_prefix10 :
    ttFiber50StateAt 10 ∈ chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 2 ∈
      chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix9 = ttFiber50Prefix2 ++ [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9]
      (chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 2) ttFiber50State2_in_pass1_prefix2
  rw [show ttFiber50Prefix10 = ttFiber50Prefix9 ++ [ttFiber50StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 10) []
    (chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 2) hparentBefore ttFiber50ReverseSingleStep10

theorem ttFiber50State10_in_pass1_full :
    ttFiber50StateAt 10 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix10 ++ [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 10) ttFiber50State10_in_pass1_prefix10

theorem ttFiber50State11_in_pass1_prefix11 :
    ttFiber50StateAt 11 ∈ chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 3 ∈
      chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix10 = ttFiber50Prefix3 ++ [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10]
      (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 3) ttFiber50State3_in_pass1_prefix3
  rw [show ttFiber50Prefix11 = ttFiber50Prefix10 ++ [ttFiber50StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 11) []
    (chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 3) hparentBefore ttFiber50ReverseSingleStep11

theorem ttFiber50State11_in_pass1_full :
    ttFiber50StateAt 11 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix11 ++ [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 11) ttFiber50State11_in_pass1_prefix11

theorem ttFiber50State12_in_pass1_prefix12 :
    ttFiber50StateAt 12 ∈ chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 4 ∈
      chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix11 = ttFiber50Prefix4 ++ [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11]
      (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 4) ttFiber50State4_in_pass1_prefix4
  rw [show ttFiber50Prefix12 = ttFiber50Prefix11 ++ [ttFiber50StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 12) []
    (chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 4) hparentBefore ttFiber50ReverseSingleStep12

theorem ttFiber50State12_in_pass1_full :
    ttFiber50StateAt 12 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix12 ++ [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 12) ttFiber50State12_in_pass1_prefix12

theorem ttFiber50State13_in_pass1_prefix13 :
    ttFiber50StateAt 13 ∈ chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 5 ∈
      chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix12 = ttFiber50Prefix5 ++ [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12]
      (chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 5) ttFiber50State5_in_pass1_prefix5
  rw [show ttFiber50Prefix13 = ttFiber50Prefix12 ++ [ttFiber50StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 13) []
    (chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 5) hparentBefore ttFiber50ReverseSingleStep13

theorem ttFiber50State13_in_pass1_full :
    ttFiber50StateAt 13 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix13 ++ [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 13) ttFiber50State13_in_pass1_prefix13

theorem ttFiber50State14_in_pass1_prefix14 :
    ttFiber50StateAt 14 ∈ chainClosureStep ttWord ttFiber50Prefix14 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 6 ∈
      chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix13 = ttFiber50Prefix6 ++ [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13]
      (chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 6) ttFiber50State6_in_pass1_prefix6
  rw [show ttFiber50Prefix14 = ttFiber50Prefix13 ++ [ttFiber50StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 14) []
    (chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 6) hparentBefore ttFiber50ReverseSingleStep14

theorem ttFiber50State14_in_pass1_full :
    ttFiber50StateAt 14 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix14 ++ [ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix14 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 14) ttFiber50State14_in_pass1_prefix14

theorem ttFiber50State15_in_pass1_prefix15 :
    ttFiber50StateAt 15 ∈ chainClosureStep ttWord ttFiber50Prefix15 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 7 ∈
      chainClosureStep ttWord ttFiber50Prefix14 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix14 = ttFiber50Prefix7 ++ [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14]
      (chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 7) ttFiber50State7_in_pass1_prefix7
  rw [show ttFiber50Prefix15 = ttFiber50Prefix14 ++ [ttFiber50StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 15) []
    (chainClosureStep ttWord ttFiber50Prefix14 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 7) hparentBefore ttFiber50ReverseSingleStep15

theorem ttFiber50State15_in_pass1_full :
    ttFiber50StateAt 15 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix15 ++ [ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix15 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 15) ttFiber50State15_in_pass1_prefix15

theorem ttFiber50State18_in_pass1_prefix18 :
    ttFiber50StateAt 18 ∈ chainClosureStep ttWord ttFiber50Prefix18 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 12 ∈
      chainClosureStep ttWord ttFiber50Prefix17 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix17 = ttFiber50Prefix12 ++ [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17]
      (chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 12) ttFiber50State12_in_pass1_prefix12
  rw [show ttFiber50Prefix18 = ttFiber50Prefix17 ++ [ttFiber50StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 18) []
    (chainClosureStep ttWord ttFiber50Prefix17 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 12) hparentBefore ttFiber50ReverseSingleStep18

theorem ttFiber50State18_in_pass1_full :
    ttFiber50StateAt 18 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix18 ++ [ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix18 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 18) ttFiber50State18_in_pass1_prefix18

theorem ttFiber50State19_in_pass1_prefix19 :
    ttFiber50StateAt 19 ∈ chainClosureStep ttWord ttFiber50Prefix19 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 13 ∈
      chainClosureStep ttWord ttFiber50Prefix18 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix18 = ttFiber50Prefix13 ++ [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18]
      (chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 13) ttFiber50State13_in_pass1_prefix13
  rw [show ttFiber50Prefix19 = ttFiber50Prefix18 ++ [ttFiber50StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 19) []
    (chainClosureStep ttWord ttFiber50Prefix18 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 13) hparentBefore ttFiber50ReverseSingleStep19

theorem ttFiber50State19_in_pass1_full :
    ttFiber50StateAt 19 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix19 ++ [ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix19 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 19) ttFiber50State19_in_pass1_prefix19

theorem ttFiber50State20_in_pass1_prefix20 :
    ttFiber50StateAt 20 ∈ chainClosureStep ttWord ttFiber50Prefix20 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 8 ∈
      chainClosureStep ttWord ttFiber50Prefix19 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix19 = ttFiber50Prefix8 ++ [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19]
      (chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 8) ttFiber50State8_in_pass1_prefix8
  rw [show ttFiber50Prefix20 = ttFiber50Prefix19 ++ [ttFiber50StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 20) []
    (chainClosureStep ttWord ttFiber50Prefix19 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 8) hparentBefore ttFiber50ReverseSingleStep20

theorem ttFiber50State20_in_pass1_full :
    ttFiber50StateAt 20 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix20 ++ [ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix20 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 20) ttFiber50State20_in_pass1_prefix20

theorem ttFiber50State21_in_pass1_prefix21 :
    ttFiber50StateAt 21 ∈ chainClosureStep ttWord ttFiber50Prefix21 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 9 ∈
      chainClosureStep ttWord ttFiber50Prefix20 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix20 = ttFiber50Prefix9 ++ [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20]
      (chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 9) ttFiber50State9_in_pass1_prefix9
  rw [show ttFiber50Prefix21 = ttFiber50Prefix20 ++ [ttFiber50StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 21) []
    (chainClosureStep ttWord ttFiber50Prefix20 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 9) hparentBefore ttFiber50ReverseSingleStep21

theorem ttFiber50State21_in_pass1_full :
    ttFiber50StateAt 21 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix21 ++ [ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix21 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 21) ttFiber50State21_in_pass1_prefix21

theorem ttFiber50State22_in_pass1_prefix22 :
    ttFiber50StateAt 22 ∈ chainClosureStep ttWord ttFiber50Prefix22 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 10 ∈
      chainClosureStep ttWord ttFiber50Prefix21 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix21 = ttFiber50Prefix10 ++ [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21]
      (chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 10) ttFiber50State10_in_pass1_prefix10
  rw [show ttFiber50Prefix22 = ttFiber50Prefix21 ++ [ttFiber50StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 22) []
    (chainClosureStep ttWord ttFiber50Prefix21 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 10) hparentBefore ttFiber50ReverseSingleStep22

theorem ttFiber50State22_in_pass1_full :
    ttFiber50StateAt 22 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix22 ++ [ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix22 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 22) ttFiber50State22_in_pass1_prefix22

theorem ttFiber50State23_in_pass1_prefix23 :
    ttFiber50StateAt 23 ∈ chainClosureStep ttWord ttFiber50Prefix23 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 11 ∈
      chainClosureStep ttWord ttFiber50Prefix22 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix22 = ttFiber50Prefix11 ++ [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22]
      (chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 11) ttFiber50State11_in_pass1_prefix11
  rw [show ttFiber50Prefix23 = ttFiber50Prefix22 ++ [ttFiber50StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 23) []
    (chainClosureStep ttWord ttFiber50Prefix22 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 11) hparentBefore ttFiber50ReverseSingleStep23

theorem ttFiber50State23_in_pass1_full :
    ttFiber50StateAt 23 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix23 ++ [ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix23 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 23) ttFiber50State23_in_pass1_prefix23

theorem ttFiber50State26_in_pass1_prefix26 :
    ttFiber50StateAt 26 ∈ chainClosureStep ttWord ttFiber50Prefix26 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 4 ∈
      chainClosureStep ttWord ttFiber50Prefix25 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix25 = ttFiber50Prefix4 ++ [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25]
      (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 4) ttFiber50State4_in_pass1_prefix4
  rw [show ttFiber50Prefix26 = ttFiber50Prefix25 ++ [ttFiber50StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 26) []
    (chainClosureStep ttWord ttFiber50Prefix25 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 4) hparentBefore ttFiber50ReverseSingleStep26

theorem ttFiber50State26_in_pass1_full :
    ttFiber50StateAt 26 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix26 ++ [ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix26 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 26) ttFiber50State26_in_pass1_prefix26

theorem ttFiber50State27_in_pass1_prefix27 :
    ttFiber50StateAt 27 ∈ chainClosureStep ttWord ttFiber50Prefix27 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 5 ∈
      chainClosureStep ttWord ttFiber50Prefix26 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix26 = ttFiber50Prefix5 ++ [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26]
      (chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 5) ttFiber50State5_in_pass1_prefix5
  rw [show ttFiber50Prefix27 = ttFiber50Prefix26 ++ [ttFiber50StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 27) []
    (chainClosureStep ttWord ttFiber50Prefix26 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 5) hparentBefore ttFiber50ReverseSingleStep27

theorem ttFiber50State27_in_pass1_full :
    ttFiber50StateAt 27 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix27 ++ [ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix27 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 27) ttFiber50State27_in_pass1_prefix27

theorem ttFiber50State28_in_pass1_prefix28 :
    ttFiber50StateAt 28 ∈ chainClosureStep ttWord ttFiber50Prefix28 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix27 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix27
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix28 = ttFiber50Prefix27 ++ [ttFiber50StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 28) []
    (chainClosureStep ttWord ttFiber50Prefix27 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep28

theorem ttFiber50State28_in_pass1_full :
    ttFiber50StateAt 28 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix28 ++ [ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix28 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 28) ttFiber50State28_in_pass1_prefix28

theorem ttFiber50State29_in_pass1_prefix29 :
    ttFiber50StateAt 29 ∈ chainClosureStep ttWord ttFiber50Prefix29 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50Prefix28 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix28 = ttFiber50Prefix1 ++ [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28]
      (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1
  rw [show ttFiber50Prefix29 = ttFiber50Prefix28 ++ [ttFiber50StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 29) []
    (chainClosureStep ttWord ttFiber50Prefix28 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) hparentBefore ttFiber50ReverseSingleStep29

theorem ttFiber50State29_in_pass1_full :
    ttFiber50StateAt 29 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix29 ++ [ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix29 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 29) ttFiber50State29_in_pass1_prefix29

theorem ttFiber50State30_in_pass1_prefix30 :
    ttFiber50StateAt 30 ∈ chainClosureStep ttWord ttFiber50Prefix30 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 2 ∈
      chainClosureStep ttWord ttFiber50Prefix29 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix29 = ttFiber50Prefix2 ++ [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29]
      (chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 2) ttFiber50State2_in_pass1_prefix2
  rw [show ttFiber50Prefix30 = ttFiber50Prefix29 ++ [ttFiber50StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 30) []
    (chainClosureStep ttWord ttFiber50Prefix29 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 2) hparentBefore ttFiber50ReverseSingleStep30

theorem ttFiber50State30_in_pass1_full :
    ttFiber50StateAt 30 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix30 ++ [ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix30 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 30) ttFiber50State30_in_pass1_prefix30

theorem ttFiber50State31_in_pass1_prefix31 :
    ttFiber50StateAt 31 ∈ chainClosureStep ttWord ttFiber50Prefix31 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 3 ∈
      chainClosureStep ttWord ttFiber50Prefix30 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix30 = ttFiber50Prefix3 ++ [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30]
      (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 3) ttFiber50State3_in_pass1_prefix3
  rw [show ttFiber50Prefix31 = ttFiber50Prefix30 ++ [ttFiber50StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 31) []
    (chainClosureStep ttWord ttFiber50Prefix30 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 3) hparentBefore ttFiber50ReverseSingleStep31

theorem ttFiber50State31_in_pass1_full :
    ttFiber50StateAt 31 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix31 ++ [ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix31 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 31) ttFiber50State31_in_pass1_prefix31

theorem ttFiber50State32_in_pass1_prefix32 :
    ttFiber50StateAt 32 ∈ chainClosureStep ttWord ttFiber50Prefix32 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 0 ∈
      chainClosureStep ttWord ttFiber50Prefix31 ([ttFiber50StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix31
      ([ttFiber50StateAt 0]) (ttFiber50StateAt 0) ttFiber50State0_in_pass0_full
  rw [show ttFiber50Prefix32 = ttFiber50Prefix31 ++ [ttFiber50StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 32) []
    (chainClosureStep ttWord ttFiber50Prefix31 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 0) hparentBefore ttFiber50ReverseSingleStep32

theorem ttFiber50State32_in_pass1_full :
    ttFiber50StateAt 32 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix32 ++ [ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix32 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 32) ttFiber50State32_in_pass1_prefix32

theorem ttFiber50State33_in_pass1_prefix33 :
    ttFiber50StateAt 33 ∈ chainClosureStep ttWord ttFiber50Prefix33 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 1 ∈
      chainClosureStep ttWord ttFiber50Prefix32 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix32 = ttFiber50Prefix1 ++ [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 2, ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32]
      (chainClosureStep ttWord ttFiber50Prefix1 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 1) ttFiber50State1_in_pass1_prefix1
  rw [show ttFiber50Prefix33 = ttFiber50Prefix32 ++ [ttFiber50StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 33) []
    (chainClosureStep ttWord ttFiber50Prefix32 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 1) hparentBefore ttFiber50ReverseSingleStep33

theorem ttFiber50State33_in_pass1_full :
    ttFiber50StateAt 33 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix33 ++ [ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix33 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 33) ttFiber50State33_in_pass1_prefix33

theorem ttFiber50State34_in_pass1_prefix34 :
    ttFiber50StateAt 34 ∈ chainClosureStep ttWord ttFiber50Prefix34 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 2 ∈
      chainClosureStep ttWord ttFiber50Prefix33 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix33 = ttFiber50Prefix2 ++ [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 3, ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33]
      (chainClosureStep ttWord ttFiber50Prefix2 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 2) ttFiber50State2_in_pass1_prefix2
  rw [show ttFiber50Prefix34 = ttFiber50Prefix33 ++ [ttFiber50StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 34) []
    (chainClosureStep ttWord ttFiber50Prefix33 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 2) hparentBefore ttFiber50ReverseSingleStep34

theorem ttFiber50State34_in_pass1_full :
    ttFiber50StateAt 34 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix34 ++ [ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix34 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 34) ttFiber50State34_in_pass1_prefix34

theorem ttFiber50State35_in_pass1_prefix35 :
    ttFiber50StateAt 35 ∈ chainClosureStep ttWord ttFiber50Prefix35 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 3 ∈
      chainClosureStep ttWord ttFiber50Prefix34 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix34 = ttFiber50Prefix3 ++ [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 4, ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34]
      (chainClosureStep ttWord ttFiber50Prefix3 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 3) ttFiber50State3_in_pass1_prefix3
  rw [show ttFiber50Prefix35 = ttFiber50Prefix34 ++ [ttFiber50StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 35) []
    (chainClosureStep ttWord ttFiber50Prefix34 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 3) hparentBefore ttFiber50ReverseSingleStep35

theorem ttFiber50State35_in_pass1_full :
    ttFiber50StateAt 35 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix35 ++ [ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix35 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 35) ttFiber50State35_in_pass1_prefix35

theorem ttFiber50State36_in_pass1_prefix36 :
    ttFiber50StateAt 36 ∈ chainClosureStep ttWord ttFiber50Prefix36 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 4 ∈
      chainClosureStep ttWord ttFiber50Prefix35 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix35 = ttFiber50Prefix4 ++ [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 5, ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35]
      (chainClosureStep ttWord ttFiber50Prefix4 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 4) ttFiber50State4_in_pass1_prefix4
  rw [show ttFiber50Prefix36 = ttFiber50Prefix35 ++ [ttFiber50StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 36) []
    (chainClosureStep ttWord ttFiber50Prefix35 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 4) hparentBefore ttFiber50ReverseSingleStep36

theorem ttFiber50State36_in_pass1_full :
    ttFiber50StateAt 36 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix36 ++ [ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix36 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 36) ttFiber50State36_in_pass1_prefix36

theorem ttFiber50State37_in_pass1_prefix37 :
    ttFiber50StateAt 37 ∈ chainClosureStep ttWord ttFiber50Prefix37 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 5 ∈
      chainClosureStep ttWord ttFiber50Prefix36 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix36 = ttFiber50Prefix5 ++ [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 6, ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36]
      (chainClosureStep ttWord ttFiber50Prefix5 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 5) ttFiber50State5_in_pass1_prefix5
  rw [show ttFiber50Prefix37 = ttFiber50Prefix36 ++ [ttFiber50StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 37) []
    (chainClosureStep ttWord ttFiber50Prefix36 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 5) hparentBefore ttFiber50ReverseSingleStep37

theorem ttFiber50State37_in_pass1_full :
    ttFiber50StateAt 37 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix37 ++ [ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix37 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 37) ttFiber50State37_in_pass1_prefix37

theorem ttFiber50State38_in_pass1_prefix38 :
    ttFiber50StateAt 38 ∈ chainClosureStep ttWord ttFiber50Prefix38 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 6 ∈
      chainClosureStep ttWord ttFiber50Prefix37 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix37 = ttFiber50Prefix6 ++ [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 7, ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37]
      (chainClosureStep ttWord ttFiber50Prefix6 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 6) ttFiber50State6_in_pass1_prefix6
  rw [show ttFiber50Prefix38 = ttFiber50Prefix37 ++ [ttFiber50StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 38) []
    (chainClosureStep ttWord ttFiber50Prefix37 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 6) hparentBefore ttFiber50ReverseSingleStep38

theorem ttFiber50State38_in_pass1_full :
    ttFiber50StateAt 38 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix38 ++ [ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix38 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 38) ttFiber50State38_in_pass1_prefix38

theorem ttFiber50State39_in_pass1_prefix39 :
    ttFiber50StateAt 39 ∈ chainClosureStep ttWord ttFiber50Prefix39 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 7 ∈
      chainClosureStep ttWord ttFiber50Prefix38 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix38 = ttFiber50Prefix7 ++ [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 8, ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38]
      (chainClosureStep ttWord ttFiber50Prefix7 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 7) ttFiber50State7_in_pass1_prefix7
  rw [show ttFiber50Prefix39 = ttFiber50Prefix38 ++ [ttFiber50StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 39) []
    (chainClosureStep ttWord ttFiber50Prefix38 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 7) hparentBefore ttFiber50ReverseSingleStep39

theorem ttFiber50State39_in_pass1_full :
    ttFiber50StateAt 39 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix39 ++ [ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix39 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 39) ttFiber50State39_in_pass1_prefix39

theorem ttFiber50State40_in_pass1_prefix40 :
    ttFiber50StateAt 40 ∈ chainClosureStep ttWord ttFiber50Prefix40 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 8 ∈
      chainClosureStep ttWord ttFiber50Prefix39 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix39 = ttFiber50Prefix8 ++ [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 9, ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39]
      (chainClosureStep ttWord ttFiber50Prefix8 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 8) ttFiber50State8_in_pass1_prefix8
  rw [show ttFiber50Prefix40 = ttFiber50Prefix39 ++ [ttFiber50StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 40) []
    (chainClosureStep ttWord ttFiber50Prefix39 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 8) hparentBefore ttFiber50ReverseSingleStep40

theorem ttFiber50State40_in_pass1_full :
    ttFiber50StateAt 40 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix40 ++ [ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix40 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 40) ttFiber50State40_in_pass1_prefix40

theorem ttFiber50State41_in_pass1_prefix41 :
    ttFiber50StateAt 41 ∈ chainClosureStep ttWord ttFiber50Prefix41 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 9 ∈
      chainClosureStep ttWord ttFiber50Prefix40 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix40 = ttFiber50Prefix9 ++ [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 10, ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40]
      (chainClosureStep ttWord ttFiber50Prefix9 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 9) ttFiber50State9_in_pass1_prefix9
  rw [show ttFiber50Prefix41 = ttFiber50Prefix40 ++ [ttFiber50StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 41) []
    (chainClosureStep ttWord ttFiber50Prefix40 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 9) hparentBefore ttFiber50ReverseSingleStep41

theorem ttFiber50State41_in_pass1_full :
    ttFiber50StateAt 41 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix41 ++ [ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix41 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 41) ttFiber50State41_in_pass1_prefix41

theorem ttFiber50State42_in_pass1_prefix42 :
    ttFiber50StateAt 42 ∈ chainClosureStep ttWord ttFiber50Prefix42 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 10 ∈
      chainClosureStep ttWord ttFiber50Prefix41 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix41 = ttFiber50Prefix10 ++ [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 11, ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41]
      (chainClosureStep ttWord ttFiber50Prefix10 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 10) ttFiber50State10_in_pass1_prefix10
  rw [show ttFiber50Prefix42 = ttFiber50Prefix41 ++ [ttFiber50StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 42) []
    (chainClosureStep ttWord ttFiber50Prefix41 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 10) hparentBefore ttFiber50ReverseSingleStep42

theorem ttFiber50State42_in_pass1_full :
    ttFiber50StateAt 42 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix42 ++ [ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix42 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 42) ttFiber50State42_in_pass1_prefix42

theorem ttFiber50State43_in_pass1_prefix43 :
    ttFiber50StateAt 43 ∈ chainClosureStep ttWord ttFiber50Prefix43 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 11 ∈
      chainClosureStep ttWord ttFiber50Prefix42 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix42 = ttFiber50Prefix11 ++ [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 12, ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42]
      (chainClosureStep ttWord ttFiber50Prefix11 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 11) ttFiber50State11_in_pass1_prefix11
  rw [show ttFiber50Prefix43 = ttFiber50Prefix42 ++ [ttFiber50StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 43) []
    (chainClosureStep ttWord ttFiber50Prefix42 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 11) hparentBefore ttFiber50ReverseSingleStep43

theorem ttFiber50State43_in_pass1_full :
    ttFiber50StateAt 43 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix43 ++ [ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix43 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 43) ttFiber50State43_in_pass1_prefix43

theorem ttFiber50State44_in_pass1_prefix44 :
    ttFiber50StateAt 44 ∈ chainClosureStep ttWord ttFiber50Prefix44 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 12 ∈
      chainClosureStep ttWord ttFiber50Prefix43 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix43 = ttFiber50Prefix12 ++ [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 13, ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43]
      (chainClosureStep ttWord ttFiber50Prefix12 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 12) ttFiber50State12_in_pass1_prefix12
  rw [show ttFiber50Prefix44 = ttFiber50Prefix43 ++ [ttFiber50StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 44) []
    (chainClosureStep ttWord ttFiber50Prefix43 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 12) hparentBefore ttFiber50ReverseSingleStep44

theorem ttFiber50State44_in_pass1_full :
    ttFiber50StateAt 44 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix44 ++ [ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix44 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 44) ttFiber50State44_in_pass1_prefix44

theorem ttFiber50State45_in_pass1_prefix45 :
    ttFiber50StateAt 45 ∈ chainClosureStep ttWord ttFiber50Prefix45 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 13 ∈
      chainClosureStep ttWord ttFiber50Prefix44 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix44 = ttFiber50Prefix13 ++ [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 14, ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44]
      (chainClosureStep ttWord ttFiber50Prefix13 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 13) ttFiber50State13_in_pass1_prefix13
  rw [show ttFiber50Prefix45 = ttFiber50Prefix44 ++ [ttFiber50StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 45) []
    (chainClosureStep ttWord ttFiber50Prefix44 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 13) hparentBefore ttFiber50ReverseSingleStep45

theorem ttFiber50State45_in_pass1_full :
    ttFiber50StateAt 45 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix45 ++ [ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix45 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 45) ttFiber50State45_in_pass1_prefix45

theorem ttFiber50State46_in_pass1_prefix46 :
    ttFiber50StateAt 46 ∈ chainClosureStep ttWord ttFiber50Prefix46 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 14 ∈
      chainClosureStep ttWord ttFiber50Prefix45 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix45 = ttFiber50Prefix14 ++ [ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 15, ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45]
      (chainClosureStep ttWord ttFiber50Prefix14 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 14) ttFiber50State14_in_pass1_prefix14
  rw [show ttFiber50Prefix46 = ttFiber50Prefix45 ++ [ttFiber50StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 46) []
    (chainClosureStep ttWord ttFiber50Prefix45 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 14) hparentBefore ttFiber50ReverseSingleStep46

theorem ttFiber50State46_in_pass1_full :
    ttFiber50StateAt 46 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix46 ++ [ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix46 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 46) ttFiber50State46_in_pass1_prefix46

theorem ttFiber50State47_in_pass1_prefix47 :
    ttFiber50StateAt 47 ∈ chainClosureStep ttWord ttFiber50Prefix47 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 15 ∈
      chainClosureStep ttWord ttFiber50Prefix46 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix46 = ttFiber50Prefix15 ++ [ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 16, ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46]
      (chainClosureStep ttWord ttFiber50Prefix15 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 15) ttFiber50State15_in_pass1_prefix15
  rw [show ttFiber50Prefix47 = ttFiber50Prefix46 ++ [ttFiber50StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 47) []
    (chainClosureStep ttWord ttFiber50Prefix46 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 15) hparentBefore ttFiber50ReverseSingleStep47

theorem ttFiber50State47_in_pass1_full :
    ttFiber50StateAt 47 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix47 ++ [ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix47 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 47) ttFiber50State47_in_pass1_prefix47

theorem ttFiber50State48_in_pass1_prefix48 :
    ttFiber50StateAt 48 ∈ chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 32 ∈
      chainClosureStep ttWord ttFiber50Prefix47 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix47 = ttFiber50Prefix32 ++ [ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47]
      (chainClosureStep ttWord ttFiber50Prefix32 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 32) ttFiber50State32_in_pass1_prefix32
  rw [show ttFiber50Prefix48 = ttFiber50Prefix47 ++ [ttFiber50StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 48) []
    (chainClosureStep ttWord ttFiber50Prefix47 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 32) hparentBefore ttFiber50ReverseSingleStep48

theorem ttFiber50State48_in_pass1_full :
    ttFiber50StateAt 48 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix48 ++ [ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 48) ttFiber50State48_in_pass1_prefix48

theorem ttFiber50State49_in_pass1_prefix49 :
    ttFiber50StateAt 49 ∈ chainClosureStep ttWord ttFiber50Prefix49 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 33 ∈
      chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix48 = ttFiber50Prefix33 ++ [ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48]
      (chainClosureStep ttWord ttFiber50Prefix33 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 33) ttFiber50State33_in_pass1_prefix33
  rw [show ttFiber50Prefix49 = ttFiber50Prefix48 ++ [ttFiber50StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 49) []
    (chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 33) hparentBefore ttFiber50ReverseSingleStep49

theorem ttFiber50State49_in_pass1_full :
    ttFiber50StateAt 49 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix49 ++ [ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix49 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 49) ttFiber50State49_in_pass1_prefix49

theorem ttFiber50State50_in_pass1_prefix50 :
    ttFiber50StateAt 50 ∈ chainClosureStep ttWord ttFiber50Prefix50 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 48 ∈
      chainClosureStep ttWord ttFiber50Prefix49 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix49 = ttFiber50Prefix48 ++ [ttFiber50StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 49]
      (chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 48) ttFiber50State48_in_pass1_prefix48
  rw [show ttFiber50Prefix50 = ttFiber50Prefix49 ++ [ttFiber50StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 50) []
    (chainClosureStep ttWord ttFiber50Prefix49 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 48) hparentBefore ttFiber50ReverseSingleStep50

theorem ttFiber50State50_in_pass1_full :
    ttFiber50StateAt 50 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix50 ++ [ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix50 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 50) ttFiber50State50_in_pass1_prefix50

theorem ttFiber50State51_in_pass1_prefix51 :
    ttFiber50StateAt 51 ∈ chainClosureStep ttWord ttFiber50Prefix51 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 35 ∈
      chainClosureStep ttWord ttFiber50Prefix50 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix50 = ttFiber50Prefix35 ++ [ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50]
      (chainClosureStep ttWord ttFiber50Prefix35 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 35) ttFiber50State35_in_pass1_prefix35
  rw [show ttFiber50Prefix51 = ttFiber50Prefix50 ++ [ttFiber50StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 51) []
    (chainClosureStep ttWord ttFiber50Prefix50 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 35) hparentBefore ttFiber50ReverseSingleStep51

theorem ttFiber50State51_in_pass1_full :
    ttFiber50StateAt 51 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix51 ++ [ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix51 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 51) ttFiber50State51_in_pass1_prefix51

theorem ttFiber50State52_in_pass1_prefix52 :
    ttFiber50StateAt 52 ∈ chainClosureStep ttWord ttFiber50Prefix52 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 36 ∈
      chainClosureStep ttWord ttFiber50Prefix51 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix51 = ttFiber50Prefix36 ++ [ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51]
      (chainClosureStep ttWord ttFiber50Prefix36 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 36) ttFiber50State36_in_pass1_prefix36
  rw [show ttFiber50Prefix52 = ttFiber50Prefix51 ++ [ttFiber50StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 52) []
    (chainClosureStep ttWord ttFiber50Prefix51 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 36) hparentBefore ttFiber50ReverseSingleStep52

theorem ttFiber50State52_in_pass1_full :
    ttFiber50StateAt 52 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix52 ++ [ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix52 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 52) ttFiber50State52_in_pass1_prefix52

theorem ttFiber50State53_in_pass1_prefix53 :
    ttFiber50StateAt 53 ∈ chainClosureStep ttWord ttFiber50Prefix53 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 37 ∈
      chainClosureStep ttWord ttFiber50Prefix52 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix52 = ttFiber50Prefix37 ++ [ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52]
      (chainClosureStep ttWord ttFiber50Prefix37 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 37) ttFiber50State37_in_pass1_prefix37
  rw [show ttFiber50Prefix53 = ttFiber50Prefix52 ++ [ttFiber50StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 53) []
    (chainClosureStep ttWord ttFiber50Prefix52 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 37) hparentBefore ttFiber50ReverseSingleStep53

theorem ttFiber50State53_in_pass1_full :
    ttFiber50StateAt 53 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix53 ++ [ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix53 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 53) ttFiber50State53_in_pass1_prefix53

theorem ttFiber50State54_in_pass1_prefix54 :
    ttFiber50StateAt 54 ∈ chainClosureStep ttWord ttFiber50Prefix54 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 49 ∈
      chainClosureStep ttWord ttFiber50Prefix53 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix53 = ttFiber50Prefix49 ++ [ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53]
      (chainClosureStep ttWord ttFiber50Prefix49 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 49) ttFiber50State49_in_pass1_prefix49
  rw [show ttFiber50Prefix54 = ttFiber50Prefix53 ++ [ttFiber50StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 54) []
    (chainClosureStep ttWord ttFiber50Prefix53 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 49) hparentBefore ttFiber50ReverseSingleStep54

theorem ttFiber50State54_in_pass1_full :
    ttFiber50StateAt 54 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix54 ++ [ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix54 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 54) ttFiber50State54_in_pass1_prefix54

theorem ttFiber50State55_in_pass1_prefix55 :
    ttFiber50StateAt 55 ∈ chainClosureStep ttWord ttFiber50Prefix55 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 48 ∈
      chainClosureStep ttWord ttFiber50Prefix54 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix54 = ttFiber50Prefix48 ++ [ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54]
      (chainClosureStep ttWord ttFiber50Prefix48 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 48) ttFiber50State48_in_pass1_prefix48
  rw [show ttFiber50Prefix55 = ttFiber50Prefix54 ++ [ttFiber50StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 55) []
    (chainClosureStep ttWord ttFiber50Prefix54 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 48) hparentBefore ttFiber50ReverseSingleStep55

theorem ttFiber50State55_in_pass1_full :
    ttFiber50StateAt 55 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix55 ++ [ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix55 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 55) ttFiber50State55_in_pass1_prefix55

theorem ttFiber50State56_in_pass1_prefix56 :
    ttFiber50StateAt 56 ∈ chainClosureStep ttWord ttFiber50Prefix56 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 40 ∈
      chainClosureStep ttWord ttFiber50Prefix55 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix55 = ttFiber50Prefix40 ++ [ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55]
      (chainClosureStep ttWord ttFiber50Prefix40 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 40) ttFiber50State40_in_pass1_prefix40
  rw [show ttFiber50Prefix56 = ttFiber50Prefix55 ++ [ttFiber50StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 56) []
    (chainClosureStep ttWord ttFiber50Prefix55 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 40) hparentBefore ttFiber50ReverseSingleStep56

theorem ttFiber50State56_in_pass1_full :
    ttFiber50StateAt 56 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix56 ++ [ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix56 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 56) ttFiber50State56_in_pass1_prefix56

theorem ttFiber50State57_in_pass1_prefix57 :
    ttFiber50StateAt 57 ∈ chainClosureStep ttWord ttFiber50Prefix57 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 41 ∈
      chainClosureStep ttWord ttFiber50Prefix56 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix56 = ttFiber50Prefix41 ++ [ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56]
      (chainClosureStep ttWord ttFiber50Prefix41 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 41) ttFiber50State41_in_pass1_prefix41
  rw [show ttFiber50Prefix57 = ttFiber50Prefix56 ++ [ttFiber50StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 57) []
    (chainClosureStep ttWord ttFiber50Prefix56 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 41) hparentBefore ttFiber50ReverseSingleStep57

theorem ttFiber50State57_in_pass1_full :
    ttFiber50StateAt 57 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix57 ++ [ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix57 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 57) ttFiber50State57_in_pass1_prefix57

theorem ttFiber50State58_in_pass1_prefix58 :
    ttFiber50StateAt 58 ∈ chainClosureStep ttWord ttFiber50Prefix58 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 26 ∈
      chainClosureStep ttWord ttFiber50Prefix57 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix57 = ttFiber50Prefix26 ++ [ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57]
      (chainClosureStep ttWord ttFiber50Prefix26 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 26) ttFiber50State26_in_pass1_prefix26
  rw [show ttFiber50Prefix58 = ttFiber50Prefix57 ++ [ttFiber50StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 58) []
    (chainClosureStep ttWord ttFiber50Prefix57 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 26) hparentBefore ttFiber50ReverseSingleStep58

theorem ttFiber50State58_in_pass1_full :
    ttFiber50StateAt 58 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix58 ++ [ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix58 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 58) ttFiber50State58_in_pass1_prefix58

theorem ttFiber50State59_in_pass1_prefix59 :
    ttFiber50StateAt 59 ∈ chainClosureStep ttWord ttFiber50Prefix59 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 27 ∈
      chainClosureStep ttWord ttFiber50Prefix58 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix58 = ttFiber50Prefix27 ++ [ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58]
      (chainClosureStep ttWord ttFiber50Prefix27 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 27) ttFiber50State27_in_pass1_prefix27
  rw [show ttFiber50Prefix59 = ttFiber50Prefix58 ++ [ttFiber50StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 59) []
    (chainClosureStep ttWord ttFiber50Prefix58 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 27) hparentBefore ttFiber50ReverseSingleStep59

theorem ttFiber50State59_in_pass1_full :
    ttFiber50StateAt 59 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix59 ++ [ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix59 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 59) ttFiber50State59_in_pass1_prefix59

theorem ttFiber50State60_in_pass1_prefix60 :
    ttFiber50StateAt 60 ∈ chainClosureStep ttWord ttFiber50Prefix60 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 28 ∈
      chainClosureStep ttWord ttFiber50Prefix59 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix59 = ttFiber50Prefix28 ++ [ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59]
      (chainClosureStep ttWord ttFiber50Prefix28 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 28) ttFiber50State28_in_pass1_prefix28
  rw [show ttFiber50Prefix60 = ttFiber50Prefix59 ++ [ttFiber50StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 60) []
    (chainClosureStep ttWord ttFiber50Prefix59 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 28) hparentBefore ttFiber50ReverseSingleStep60

theorem ttFiber50State60_in_pass1_full :
    ttFiber50StateAt 60 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix60 ++ [ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix60 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 60) ttFiber50State60_in_pass1_prefix60

theorem ttFiber50State61_in_pass1_prefix61 :
    ttFiber50StateAt 61 ∈ chainClosureStep ttWord ttFiber50Prefix61 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 29 ∈
      chainClosureStep ttWord ttFiber50Prefix60 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix60 = ttFiber50Prefix29 ++ [ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60]
      (chainClosureStep ttWord ttFiber50Prefix29 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 29) ttFiber50State29_in_pass1_prefix29
  rw [show ttFiber50Prefix61 = ttFiber50Prefix60 ++ [ttFiber50StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 61) []
    (chainClosureStep ttWord ttFiber50Prefix60 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 29) hparentBefore ttFiber50ReverseSingleStep61

theorem ttFiber50State61_in_pass1_full :
    ttFiber50StateAt 61 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix61 ++ [ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix61 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 61) ttFiber50State61_in_pass1_prefix61

theorem ttFiber50State62_in_pass1_prefix62 :
    ttFiber50StateAt 62 ∈ chainClosureStep ttWord ttFiber50Prefix62 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 60 ∈
      chainClosureStep ttWord ttFiber50Prefix61 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix61 = ttFiber50Prefix60 ++ [ttFiber50StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 61]
      (chainClosureStep ttWord ttFiber50Prefix60 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 60) ttFiber50State60_in_pass1_prefix60
  rw [show ttFiber50Prefix62 = ttFiber50Prefix61 ++ [ttFiber50StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 62) []
    (chainClosureStep ttWord ttFiber50Prefix61 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 60) hparentBefore ttFiber50ReverseSingleStep62

theorem ttFiber50State62_in_pass1_full :
    ttFiber50StateAt 62 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix62 ++ [ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix62 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 62) ttFiber50State62_in_pass1_prefix62

theorem ttFiber50State63_in_pass1_prefix63 :
    ttFiber50StateAt 63 ∈ chainClosureStep ttWord ttFiber50Prefix63 ([ttFiber50StateAt 0]) := by
  have hparentBefore : ttFiber50StateAt 31 ∈
      chainClosureStep ttWord ttFiber50Prefix62 ([ttFiber50StateAt 0]) := by
    rw [show ttFiber50Prefix62 = ttFiber50Prefix31 ++ [ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62]
      (chainClosureStep ttWord ttFiber50Prefix31 ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 31) ttFiber50State31_in_pass1_prefix31
  rw [show ttFiber50Prefix63 = ttFiber50Prefix62 ++ [ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 63) []
    (chainClosureStep ttWord ttFiber50Prefix62 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 31) hparentBefore ttFiber50ReverseSingleStep63

theorem ttFiber50State63_in_pass1_full :
    ttFiber50StateAt 63 ∈ chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber50Prefix63 ([ttFiber50StateAt 0]))
    (ttFiber50StateAt 63) ttFiber50State63_in_pass1_prefix63

theorem ttFiber50State16_in_pass2_prefix16 :
    ttFiber50StateAt 16 ∈ chainClosureStep ttWord ttFiber50Prefix16 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  have hparentBefore : ttFiber50StateAt 20 ∈
      chainClosureStep ttWord ttFiber50Prefix15 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix15
      (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 20) ttFiber50State20_in_pass1_full
  rw [show ttFiber50Prefix16 = ttFiber50Prefix15 ++ [ttFiber50StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 16) []
    (chainClosureStep ttWord ttFiber50Prefix15 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 20) hparentBefore ttFiber50ReverseSingleStep16

theorem ttFiber50State16_in_pass2_full :
    ttFiber50StateAt 16 ∈ chainClosureStep ttWord ttFiber50DirectStates (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix16 ++ [ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 17, ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix16 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 16) ttFiber50State16_in_pass2_prefix16

theorem ttFiber50State17_in_pass2_prefix17 :
    ttFiber50StateAt 17 ∈ chainClosureStep ttWord ttFiber50Prefix17 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  have hparentBefore : ttFiber50StateAt 21 ∈
      chainClosureStep ttWord ttFiber50Prefix16 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix16
      (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 21) ttFiber50State21_in_pass1_full
  rw [show ttFiber50Prefix17 = ttFiber50Prefix16 ++ [ttFiber50StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 17) []
    (chainClosureStep ttWord ttFiber50Prefix16 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 21) hparentBefore ttFiber50ReverseSingleStep17

theorem ttFiber50State17_in_pass2_full :
    ttFiber50StateAt 17 ∈ chainClosureStep ttWord ttFiber50DirectStates (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix17 ++ [ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 18, ttFiber50StateAt 19, ttFiber50StateAt 20, ttFiber50StateAt 21, ttFiber50StateAt 22, ttFiber50StateAt 23, ttFiber50StateAt 24, ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix17 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 17) ttFiber50State17_in_pass2_prefix17

theorem ttFiber50State24_in_pass2_prefix24 :
    ttFiber50StateAt 24 ∈ chainClosureStep ttWord ttFiber50Prefix24 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  have hparentBefore : ttFiber50StateAt 28 ∈
      chainClosureStep ttWord ttFiber50Prefix23 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix23
      (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 28) ttFiber50State28_in_pass1_full
  rw [show ttFiber50Prefix24 = ttFiber50Prefix23 ++ [ttFiber50StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 24) []
    (chainClosureStep ttWord ttFiber50Prefix23 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 28) hparentBefore ttFiber50ReverseSingleStep24

theorem ttFiber50State24_in_pass2_full :
    ttFiber50StateAt 24 ∈ chainClosureStep ttWord ttFiber50DirectStates (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix24 ++ [ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 25, ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix24 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 24) ttFiber50State24_in_pass2_prefix24

theorem ttFiber50State25_in_pass2_prefix25 :
    ttFiber50StateAt 25 ∈ chainClosureStep ttWord ttFiber50Prefix25 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  have hparentBefore : ttFiber50StateAt 29 ∈
      chainClosureStep ttWord ttFiber50Prefix24 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber50Prefix24
      (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0]))
      (ttFiber50StateAt 29) ttFiber50State29_in_pass1_full
  rw [show ttFiber50Prefix25 = ttFiber50Prefix24 ++ [ttFiber50StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber50StateAt 25) []
    (chainClosureStep ttWord ttFiber50Prefix24 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 29) hparentBefore ttFiber50ReverseSingleStep25

theorem ttFiber50State25_in_pass2_full :
    ttFiber50StateAt 25 ∈ chainClosureStep ttWord ttFiber50DirectStates (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])) := by
  rw [show ttFiber50DirectStates = ttFiber50Prefix25 ++ [ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber50StateAt 26, ttFiber50StateAt 27, ttFiber50StateAt 28, ttFiber50StateAt 29, ttFiber50StateAt 30, ttFiber50StateAt 31, ttFiber50StateAt 32, ttFiber50StateAt 33, ttFiber50StateAt 34, ttFiber50StateAt 35, ttFiber50StateAt 36, ttFiber50StateAt 37, ttFiber50StateAt 38, ttFiber50StateAt 39, ttFiber50StateAt 40, ttFiber50StateAt 41, ttFiber50StateAt 42, ttFiber50StateAt 43, ttFiber50StateAt 44, ttFiber50StateAt 45, ttFiber50StateAt 46, ttFiber50StateAt 47, ttFiber50StateAt 48, ttFiber50StateAt 49, ttFiber50StateAt 50, ttFiber50StateAt 51, ttFiber50StateAt 52, ttFiber50StateAt 53, ttFiber50StateAt 54, ttFiber50StateAt 55, ttFiber50StateAt 56, ttFiber50StateAt 57, ttFiber50StateAt 58, ttFiber50StateAt 59, ttFiber50StateAt 60, ttFiber50StateAt 61, ttFiber50StateAt 62, ttFiber50StateAt 63]
    (chainClosureStep ttWord ttFiber50Prefix25 (chainClosureStep ttWord ttFiber50DirectStates ([ttFiber50StateAt 0])))
    (ttFiber50StateAt 25) ttFiber50State25_in_pass2_prefix25

theorem ttFiber50State0_in_close :
    ttFiber50StateAt 0 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber50DirectStates ttFiber50DirectStates.length
    [ttFiber50StateAt 0] (ttFiber50StateAt 0) (by simp)

theorem ttFiber50State1_in_close :
    ttFiber50StateAt 1 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 1 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 1) ttFiber50State1_in_pass1_full

theorem ttFiber50State2_in_close :
    ttFiber50StateAt 2 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 2 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 2) ttFiber50State2_in_pass1_full

theorem ttFiber50State3_in_close :
    ttFiber50StateAt 3 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 3 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 3) ttFiber50State3_in_pass1_full

theorem ttFiber50State4_in_close :
    ttFiber50StateAt 4 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 4 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 4) ttFiber50State4_in_pass1_full

theorem ttFiber50State5_in_close :
    ttFiber50StateAt 5 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 5 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 5) ttFiber50State5_in_pass1_full

theorem ttFiber50State6_in_close :
    ttFiber50StateAt 6 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 6 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 6) ttFiber50State6_in_pass1_full

theorem ttFiber50State7_in_close :
    ttFiber50StateAt 7 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 7 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 7) ttFiber50State7_in_pass1_full

theorem ttFiber50State8_in_close :
    ttFiber50StateAt 8 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 8 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 8) ttFiber50State8_in_pass1_full

theorem ttFiber50State9_in_close :
    ttFiber50StateAt 9 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 9 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 9) ttFiber50State9_in_pass1_full

theorem ttFiber50State10_in_close :
    ttFiber50StateAt 10 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 10 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 10) ttFiber50State10_in_pass1_full

theorem ttFiber50State11_in_close :
    ttFiber50StateAt 11 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 11 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 11) ttFiber50State11_in_pass1_full

theorem ttFiber50State12_in_close :
    ttFiber50StateAt 12 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 12 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 12) ttFiber50State12_in_pass1_full

theorem ttFiber50State13_in_close :
    ttFiber50StateAt 13 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 13 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 13) ttFiber50State13_in_pass1_full

theorem ttFiber50State14_in_close :
    ttFiber50StateAt 14 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 14 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 14) ttFiber50State14_in_pass1_full

theorem ttFiber50State15_in_close :
    ttFiber50StateAt 15 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 15 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 15) ttFiber50State15_in_pass1_full

theorem ttFiber50State16_in_close :
    ttFiber50StateAt 16 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 16 ∈ closeChainFiber ttWord ttFiber50DirectStates (62 + 2)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber50DirectStates 62
    [ttFiber50StateAt 0] (ttFiber50StateAt 16) ttFiber50FirstPassGrows
    ttFiber50State16_in_pass2_full

theorem ttFiber50State17_in_close :
    ttFiber50StateAt 17 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 17 ∈ closeChainFiber ttWord ttFiber50DirectStates (62 + 2)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber50DirectStates 62
    [ttFiber50StateAt 0] (ttFiber50StateAt 17) ttFiber50FirstPassGrows
    ttFiber50State17_in_pass2_full

theorem ttFiber50State18_in_close :
    ttFiber50StateAt 18 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 18 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 18) ttFiber50State18_in_pass1_full

theorem ttFiber50State19_in_close :
    ttFiber50StateAt 19 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 19 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 19) ttFiber50State19_in_pass1_full

theorem ttFiber50State20_in_close :
    ttFiber50StateAt 20 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 20 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 20) ttFiber50State20_in_pass1_full

theorem ttFiber50State21_in_close :
    ttFiber50StateAt 21 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 21 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 21) ttFiber50State21_in_pass1_full

theorem ttFiber50State22_in_close :
    ttFiber50StateAt 22 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 22 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 22) ttFiber50State22_in_pass1_full

theorem ttFiber50State23_in_close :
    ttFiber50StateAt 23 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 23 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 23) ttFiber50State23_in_pass1_full

theorem ttFiber50State24_in_close :
    ttFiber50StateAt 24 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 24 ∈ closeChainFiber ttWord ttFiber50DirectStates (62 + 2)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber50DirectStates 62
    [ttFiber50StateAt 0] (ttFiber50StateAt 24) ttFiber50FirstPassGrows
    ttFiber50State24_in_pass2_full

theorem ttFiber50State25_in_close :
    ttFiber50StateAt 25 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 25 ∈ closeChainFiber ttWord ttFiber50DirectStates (62 + 2)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber50DirectStates 62
    [ttFiber50StateAt 0] (ttFiber50StateAt 25) ttFiber50FirstPassGrows
    ttFiber50State25_in_pass2_full

theorem ttFiber50State26_in_close :
    ttFiber50StateAt 26 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 26 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 26) ttFiber50State26_in_pass1_full

theorem ttFiber50State27_in_close :
    ttFiber50StateAt 27 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 27 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 27) ttFiber50State27_in_pass1_full

theorem ttFiber50State28_in_close :
    ttFiber50StateAt 28 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 28 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 28) ttFiber50State28_in_pass1_full

theorem ttFiber50State29_in_close :
    ttFiber50StateAt 29 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 29 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 29) ttFiber50State29_in_pass1_full

theorem ttFiber50State30_in_close :
    ttFiber50StateAt 30 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 30 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 30) ttFiber50State30_in_pass1_full

theorem ttFiber50State31_in_close :
    ttFiber50StateAt 31 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 31 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 31) ttFiber50State31_in_pass1_full

theorem ttFiber50State32_in_close :
    ttFiber50StateAt 32 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 32 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 32) ttFiber50State32_in_pass1_full

theorem ttFiber50State33_in_close :
    ttFiber50StateAt 33 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 33 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 33) ttFiber50State33_in_pass1_full

theorem ttFiber50State34_in_close :
    ttFiber50StateAt 34 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 34 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 34) ttFiber50State34_in_pass1_full

theorem ttFiber50State35_in_close :
    ttFiber50StateAt 35 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 35 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 35) ttFiber50State35_in_pass1_full

theorem ttFiber50State36_in_close :
    ttFiber50StateAt 36 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 36 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 36) ttFiber50State36_in_pass1_full

theorem ttFiber50State37_in_close :
    ttFiber50StateAt 37 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 37 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 37) ttFiber50State37_in_pass1_full

theorem ttFiber50State38_in_close :
    ttFiber50StateAt 38 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 38 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 38) ttFiber50State38_in_pass1_full

theorem ttFiber50State39_in_close :
    ttFiber50StateAt 39 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 39 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 39) ttFiber50State39_in_pass1_full

theorem ttFiber50State40_in_close :
    ttFiber50StateAt 40 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 40 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 40) ttFiber50State40_in_pass1_full

theorem ttFiber50State41_in_close :
    ttFiber50StateAt 41 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 41 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 41) ttFiber50State41_in_pass1_full

theorem ttFiber50State42_in_close :
    ttFiber50StateAt 42 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 42 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 42) ttFiber50State42_in_pass1_full

theorem ttFiber50State43_in_close :
    ttFiber50StateAt 43 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 43 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 43) ttFiber50State43_in_pass1_full

theorem ttFiber50State44_in_close :
    ttFiber50StateAt 44 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 44 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 44) ttFiber50State44_in_pass1_full

theorem ttFiber50State45_in_close :
    ttFiber50StateAt 45 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 45 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 45) ttFiber50State45_in_pass1_full

theorem ttFiber50State46_in_close :
    ttFiber50StateAt 46 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 46 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 46) ttFiber50State46_in_pass1_full

theorem ttFiber50State47_in_close :
    ttFiber50StateAt 47 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 47 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 47) ttFiber50State47_in_pass1_full

theorem ttFiber50State48_in_close :
    ttFiber50StateAt 48 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 48 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 48) ttFiber50State48_in_pass1_full

theorem ttFiber50State49_in_close :
    ttFiber50StateAt 49 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 49 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 49) ttFiber50State49_in_pass1_full

theorem ttFiber50State50_in_close :
    ttFiber50StateAt 50 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 50 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 50) ttFiber50State50_in_pass1_full

theorem ttFiber50State51_in_close :
    ttFiber50StateAt 51 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 51 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 51) ttFiber50State51_in_pass1_full

theorem ttFiber50State52_in_close :
    ttFiber50StateAt 52 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 52 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 52) ttFiber50State52_in_pass1_full

theorem ttFiber50State53_in_close :
    ttFiber50StateAt 53 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 53 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 53) ttFiber50State53_in_pass1_full

theorem ttFiber50State54_in_close :
    ttFiber50StateAt 54 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 54 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 54) ttFiber50State54_in_pass1_full

theorem ttFiber50State55_in_close :
    ttFiber50StateAt 55 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 55 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 55) ttFiber50State55_in_pass1_full

theorem ttFiber50State56_in_close :
    ttFiber50StateAt 56 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 56 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 56) ttFiber50State56_in_pass1_full

theorem ttFiber50State57_in_close :
    ttFiber50StateAt 57 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 57 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 57) ttFiber50State57_in_pass1_full

theorem ttFiber50State58_in_close :
    ttFiber50StateAt 58 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 58 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 58) ttFiber50State58_in_pass1_full

theorem ttFiber50State59_in_close :
    ttFiber50StateAt 59 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 59 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 59) ttFiber50State59_in_pass1_full

theorem ttFiber50State60_in_close :
    ttFiber50StateAt 60 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 60 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 60) ttFiber50State60_in_pass1_full

theorem ttFiber50State61_in_close :
    ttFiber50StateAt 61 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 61 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 61) ttFiber50State61_in_pass1_full

theorem ttFiber50State62_in_close :
    ttFiber50StateAt 62 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 62 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 62) ttFiber50State62_in_pass1_full

theorem ttFiber50State63_in_close :
    ttFiber50StateAt 63 ∈
      closeChainFiber ttWord ttFiber50DirectStates ttFiber50DirectStates.length
        [ttFiber50StateAt 0] := by
  change ttFiber50StateAt 63 ∈ closeChainFiber ttWord ttFiber50DirectStates (63 + 1)
    [ttFiber50StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber50DirectStates 63
    [ttFiber50StateAt 0] (ttFiber50StateAt 63) ttFiber50State63_in_pass1_full

theorem ttFiber50DirectConnected :
    chainFiberConnected ttWord ttFiber50DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber50DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber50State0_in_close
  · subst state
    exact ttFiber50State1_in_close
  · subst state
    exact ttFiber50State2_in_close
  · subst state
    exact ttFiber50State3_in_close
  · subst state
    exact ttFiber50State4_in_close
  · subst state
    exact ttFiber50State5_in_close
  · subst state
    exact ttFiber50State6_in_close
  · subst state
    exact ttFiber50State7_in_close
  · subst state
    exact ttFiber50State8_in_close
  · subst state
    exact ttFiber50State9_in_close
  · subst state
    exact ttFiber50State10_in_close
  · subst state
    exact ttFiber50State11_in_close
  · subst state
    exact ttFiber50State12_in_close
  · subst state
    exact ttFiber50State13_in_close
  · subst state
    exact ttFiber50State14_in_close
  · subst state
    exact ttFiber50State15_in_close
  · subst state
    exact ttFiber50State16_in_close
  · subst state
    exact ttFiber50State17_in_close
  · subst state
    exact ttFiber50State18_in_close
  · subst state
    exact ttFiber50State19_in_close
  · subst state
    exact ttFiber50State20_in_close
  · subst state
    exact ttFiber50State21_in_close
  · subst state
    exact ttFiber50State22_in_close
  · subst state
    exact ttFiber50State23_in_close
  · subst state
    exact ttFiber50State24_in_close
  · subst state
    exact ttFiber50State25_in_close
  · subst state
    exact ttFiber50State26_in_close
  · subst state
    exact ttFiber50State27_in_close
  · subst state
    exact ttFiber50State28_in_close
  · subst state
    exact ttFiber50State29_in_close
  · subst state
    exact ttFiber50State30_in_close
  · subst state
    exact ttFiber50State31_in_close
  · subst state
    exact ttFiber50State32_in_close
  · subst state
    exact ttFiber50State33_in_close
  · subst state
    exact ttFiber50State34_in_close
  · subst state
    exact ttFiber50State35_in_close
  · subst state
    exact ttFiber50State36_in_close
  · subst state
    exact ttFiber50State37_in_close
  · subst state
    exact ttFiber50State38_in_close
  · subst state
    exact ttFiber50State39_in_close
  · subst state
    exact ttFiber50State40_in_close
  · subst state
    exact ttFiber50State41_in_close
  · subst state
    exact ttFiber50State42_in_close
  · subst state
    exact ttFiber50State43_in_close
  · subst state
    exact ttFiber50State44_in_close
  · subst state
    exact ttFiber50State45_in_close
  · subst state
    exact ttFiber50State46_in_close
  · subst state
    exact ttFiber50State47_in_close
  · subst state
    exact ttFiber50State48_in_close
  · subst state
    exact ttFiber50State49_in_close
  · subst state
    exact ttFiber50State50_in_close
  · subst state
    exact ttFiber50State51_in_close
  · subst state
    exact ttFiber50State52_in_close
  · subst state
    exact ttFiber50State53_in_close
  · subst state
    exact ttFiber50State54_in_close
  · subst state
    exact ttFiber50State55_in_close
  · subst state
    exact ttFiber50State56_in_close
  · subst state
    exact ttFiber50State57_in_close
  · subst state
    exact ttFiber50State58_in_close
  · subst state
    exact ttFiber50State59_in_close
  · subst state
    exact ttFiber50State60_in_close
  · subst state
    exact ttFiber50State61_in_close
  · subst state
    exact ttFiber50State62_in_close
  · subst state
    exact ttFiber50State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
