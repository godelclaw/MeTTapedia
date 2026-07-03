import Mettapedia.GraphTheory.FourColor.GoertzelLemma818LengthTwoBase

namespace Mettapedia.GraphTheory.FourColor

/-!
# Generated multi-pass direct closure bridge for ttFiber30

This local bridge proves direct closure connectedness for one generated
length-two `tau,tau` fiber. It is generated from row-local reverse
certificate chunks and keeps Lean on default limits.
-/

namespace GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

open GoertzelLemma814
open GoertzelLemma818CompositeCertificate

def ttFiber30StateAt (i : Nat) : List TauState :=
  directStates (ttFiber30RowAt i).sourceLeft (ttFiber30RowAt i).sourceRight

def ttFiber30DirectStates : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]

def ttFiber30Prefix0 : List (List TauState) :=
  [ttFiber30StateAt 0]

def ttFiber30Prefix1 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1]

def ttFiber30Prefix2 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2]

def ttFiber30Prefix3 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3]

def ttFiber30Prefix4 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4]

def ttFiber30Prefix5 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5]

def ttFiber30Prefix6 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6]

def ttFiber30Prefix7 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7]

def ttFiber30Prefix8 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8]

def ttFiber30Prefix9 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9]

def ttFiber30Prefix10 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10]

def ttFiber30Prefix11 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11]

def ttFiber30Prefix12 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12]

def ttFiber30Prefix13 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13]

def ttFiber30Prefix14 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14]

def ttFiber30Prefix15 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15]

def ttFiber30Prefix16 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16]

def ttFiber30Prefix17 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17]

def ttFiber30Prefix18 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18]

def ttFiber30Prefix19 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19]

def ttFiber30Prefix20 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20]

def ttFiber30Prefix21 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21]

def ttFiber30Prefix22 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22]

def ttFiber30Prefix23 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23]

def ttFiber30Prefix24 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24]

def ttFiber30Prefix25 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25]

def ttFiber30Prefix26 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26]

def ttFiber30Prefix27 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27]

def ttFiber30Prefix28 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28]

def ttFiber30Prefix29 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29]

def ttFiber30Prefix30 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30]

def ttFiber30Prefix31 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31]

def ttFiber30Prefix32 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32]

def ttFiber30Prefix33 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33]

def ttFiber30Prefix34 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34]

def ttFiber30Prefix35 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35]

def ttFiber30Prefix36 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36]

def ttFiber30Prefix37 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37]

def ttFiber30Prefix38 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38]

def ttFiber30Prefix39 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39]

def ttFiber30Prefix40 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40]

def ttFiber30Prefix41 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41]

def ttFiber30Prefix42 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42]

def ttFiber30Prefix43 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43]

def ttFiber30Prefix44 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44]

def ttFiber30Prefix45 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45]

def ttFiber30Prefix46 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46]

def ttFiber30Prefix47 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47]

def ttFiber30Prefix48 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48]

def ttFiber30Prefix49 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49]

def ttFiber30Prefix50 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50]

def ttFiber30Prefix51 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51]

def ttFiber30Prefix52 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52]

def ttFiber30Prefix53 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53]

def ttFiber30Prefix54 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54]

def ttFiber30Prefix55 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55]

def ttFiber30Prefix56 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56]

def ttFiber30Prefix57 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57]

def ttFiber30Prefix58 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58]

def ttFiber30Prefix59 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59]

def ttFiber30Prefix60 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60]

def ttFiber30Prefix61 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61]

def ttFiber30Prefix62 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62]

def ttFiber30Prefix63 : List (List TauState) :=
  [ttFiber30StateAt 0, ttFiber30StateAt 1, ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]

theorem ttFiber30ReverseRow_1_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 1) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk0_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk0] at h
  exact h.2

theorem ttFiber30ReverseSingleStep1 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 1) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 1)
      (ttFiber30RowAt 1).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 1) (by decide) ttFiber30ReverseRow_1_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_2_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 2) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk1] at h
  exact h.1

theorem ttFiber30ReverseSingleStep2 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 2) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 2)
      (ttFiber30RowAt 2).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 2) (by decide) ttFiber30ReverseRow_2_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_3_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 3) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk1_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk1] at h
  exact h.2

theorem ttFiber30ReverseSingleStep3 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 3) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 3)
      (ttFiber30RowAt 3).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 3) (by decide) ttFiber30ReverseRow_3_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_4_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 4) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk2] at h
  exact h.1

theorem ttFiber30ReverseSingleStep4 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 4) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 4)
      (ttFiber30RowAt 4).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 4) (by decide) ttFiber30ReverseRow_4_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_5_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 5) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk2_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk2] at h
  exact h.2

theorem ttFiber30ReverseSingleStep5 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 5) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 5)
      (ttFiber30RowAt 5).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 5) (by decide) ttFiber30ReverseRow_5_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_6_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 6) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk3] at h
  exact h.1

theorem ttFiber30ReverseSingleStep6 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 6) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 6)
      (ttFiber30RowAt 6).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 6) (by decide) ttFiber30ReverseRow_6_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_7_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 7) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk3_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk3] at h
  exact h.2

theorem ttFiber30ReverseSingleStep7 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 7) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 7)
      (ttFiber30RowAt 7).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 7) (by decide) ttFiber30ReverseRow_7_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_8_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 8) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk4] at h
  exact h.1

theorem ttFiber30ReverseSingleStep8 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 8) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 8)
      (ttFiber30RowAt 8).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 8) (by decide) ttFiber30ReverseRow_8_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_9_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 9) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk4_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk4] at h
  exact h.2

theorem ttFiber30ReverseSingleStep9 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 9) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 9)
      (ttFiber30RowAt 9).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 9) (by decide) ttFiber30ReverseRow_9_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_10_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 10) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk5] at h
  exact h.1

theorem ttFiber30ReverseSingleStep10 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 10) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 10)
      (ttFiber30RowAt 10).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 10) (by decide) ttFiber30ReverseRow_10_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_11_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 11) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk5_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk5] at h
  exact h.2

theorem ttFiber30ReverseSingleStep11 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 3) (ttFiber30StateAt 11) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 3) (ttFiber30StateAt 11)
      (ttFiber30RowAt 11).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 11) (by decide) ttFiber30ReverseRow_11_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_12_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 12) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk6] at h
  exact h.1

theorem ttFiber30ReverseSingleStep12 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 4) (ttFiber30StateAt 12) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 4) (ttFiber30StateAt 12)
      (ttFiber30RowAt 12).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 12) (by decide) ttFiber30ReverseRow_12_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_13_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 13) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk6_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk6] at h
  exact h.2

theorem ttFiber30ReverseSingleStep13 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 5) (ttFiber30StateAt 13) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 5) (ttFiber30StateAt 13)
      (ttFiber30RowAt 13).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 13) (by decide) ttFiber30ReverseRow_13_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_14_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 14) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk7] at h
  exact h.1

theorem ttFiber30ReverseSingleStep14 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 14) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 14)
      (ttFiber30RowAt 14).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 14) (by decide) ttFiber30ReverseRow_14_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_15_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 15) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk7_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk7] at h
  exact h.2

theorem ttFiber30ReverseSingleStep15 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 15) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 15)
      (ttFiber30RowAt 15).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 15) (by decide) ttFiber30ReverseRow_15_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_16_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 16) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk8] at h
  exact h.1

theorem ttFiber30ReverseSingleStep16 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 16) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 16)
      (ttFiber30RowAt 16).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 16) (by decide) ttFiber30ReverseRow_16_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_17_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 17) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk8_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk8] at h
  exact h.2

theorem ttFiber30ReverseSingleStep17 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 17) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 17)
      (ttFiber30RowAt 17).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 17) (by decide) ttFiber30ReverseRow_17_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_18_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 18) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk9] at h
  exact h.1

theorem ttFiber30ReverseSingleStep18 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 18) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 18)
      (ttFiber30RowAt 18).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 18) (by decide) ttFiber30ReverseRow_18_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_19_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 19) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk9_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk9] at h
  exact h.2

theorem ttFiber30ReverseSingleStep19 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 3) (ttFiber30StateAt 19) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 3) (ttFiber30StateAt 19)
      (ttFiber30RowAt 19).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 19) (by decide) ttFiber30ReverseRow_19_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_20_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 20) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk10] at h
  exact h.1

theorem ttFiber30ReverseSingleStep20 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 16) (ttFiber30StateAt 20) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 16) (ttFiber30StateAt 20)
      (ttFiber30RowAt 20).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 20) (by decide) ttFiber30ReverseRow_20_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_21_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 21) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk10_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk10] at h
  exact h.2

theorem ttFiber30ReverseSingleStep21 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 17) (ttFiber30StateAt 21) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 17) (ttFiber30StateAt 21)
      (ttFiber30RowAt 21).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 21) (by decide) ttFiber30ReverseRow_21_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_22_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 22) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk11] at h
  exact h.1

theorem ttFiber30ReverseSingleStep22 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 22) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 22)
      (ttFiber30RowAt 22).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 22) (by decide) ttFiber30ReverseRow_22_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_23_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 23) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk11_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk11] at h
  exact h.2

theorem ttFiber30ReverseSingleStep23 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 23) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 23)
      (ttFiber30RowAt 23).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 23) (by decide) ttFiber30ReverseRow_23_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_24_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 24) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk12] at h
  exact h.1

theorem ttFiber30ReverseSingleStep24 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 8) (ttFiber30StateAt 24) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 8) (ttFiber30StateAt 24)
      (ttFiber30RowAt 24).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 24) (by decide) ttFiber30ReverseRow_24_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_25_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 25) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk12_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk12] at h
  exact h.2

theorem ttFiber30ReverseSingleStep25 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 9) (ttFiber30StateAt 25) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 9) (ttFiber30StateAt 25)
      (ttFiber30RowAt 25).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 25) (by decide) ttFiber30ReverseRow_25_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_26_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 26) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk13] at h
  exact h.1

theorem ttFiber30ReverseSingleStep26 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 10) (ttFiber30StateAt 26) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 10) (ttFiber30StateAt 26)
      (ttFiber30RowAt 26).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 26) (by decide) ttFiber30ReverseRow_26_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_27_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 27) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk13_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk13] at h
  exact h.2

theorem ttFiber30ReverseSingleStep27 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 11) (ttFiber30StateAt 27) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 11) (ttFiber30StateAt 27)
      (ttFiber30RowAt 27).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 27) (by decide) ttFiber30ReverseRow_27_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_28_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 28) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk14] at h
  exact h.1

theorem ttFiber30ReverseSingleStep28 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 24) (ttFiber30StateAt 28) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 24) (ttFiber30StateAt 28)
      (ttFiber30RowAt 28).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 28) (by decide) ttFiber30ReverseRow_28_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_29_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 29) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk14_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk14] at h
  exact h.2

theorem ttFiber30ReverseSingleStep29 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 25) (ttFiber30StateAt 29) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 25) (ttFiber30StateAt 29)
      (ttFiber30RowAt 29).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 29) (by decide) ttFiber30ReverseRow_29_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_30_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 30) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk15] at h
  exact h.1

theorem ttFiber30ReverseSingleStep30 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 14) (ttFiber30StateAt 30) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 14) (ttFiber30StateAt 30)
      (ttFiber30RowAt 30).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 30) (by decide) ttFiber30ReverseRow_30_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_31_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 31) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk15_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk15] at h
  exact h.2

theorem ttFiber30ReverseSingleStep31 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 15) (ttFiber30StateAt 31) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 15) (ttFiber30StateAt 31)
      (ttFiber30RowAt 31).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 31) (by decide) ttFiber30ReverseRow_31_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_32_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 32) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk16] at h
  exact h.1

theorem ttFiber30ReverseSingleStep32 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 32) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 0) (ttFiber30StateAt 32)
      (ttFiber30RowAt 32).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 32) (by decide) ttFiber30ReverseRow_32_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_33_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 33) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk16_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk16] at h
  exact h.2

theorem ttFiber30ReverseSingleStep33 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 33) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 1) (ttFiber30StateAt 33)
      (ttFiber30RowAt 33).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 33) (by decide) ttFiber30ReverseRow_33_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_34_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 34) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk17] at h
  exact h.1

theorem ttFiber30ReverseSingleStep34 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 34) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 2) (ttFiber30StateAt 34)
      (ttFiber30RowAt 34).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 34) (by decide) ttFiber30ReverseRow_34_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_35_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 35) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk17_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk17] at h
  exact h.2

theorem ttFiber30ReverseSingleStep35 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 35) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 35)
      (ttFiber30RowAt 35).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 35) (by decide) ttFiber30ReverseRow_35_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_36_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 36) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk18] at h
  exact h.1

theorem ttFiber30ReverseSingleStep36 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 36) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 36)
      (ttFiber30RowAt 36).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 36) (by decide) ttFiber30ReverseRow_36_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_37_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 37) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk18_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk18] at h
  exact h.2

theorem ttFiber30ReverseSingleStep37 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 33) (ttFiber30StateAt 37) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 33) (ttFiber30StateAt 37)
      (ttFiber30RowAt 37).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 37) (by decide) ttFiber30ReverseRow_37_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_38_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 38) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk19] at h
  exact h.1

theorem ttFiber30ReverseSingleStep38 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 38) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 6) (ttFiber30StateAt 38)
      (ttFiber30RowAt 38).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 38) (by decide) ttFiber30ReverseRow_38_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_39_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 39) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk19_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk19] at h
  exact h.2

theorem ttFiber30ReverseSingleStep39 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 39) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 7) (ttFiber30StateAt 39)
      (ttFiber30RowAt 39).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 39) (by decide) ttFiber30ReverseRow_39_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_40_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 40) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk20] at h
  exact h.1

theorem ttFiber30ReverseSingleStep40 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 8) (ttFiber30StateAt 40) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 8) (ttFiber30StateAt 40)
      (ttFiber30RowAt 40).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 40) (by decide) ttFiber30ReverseRow_40_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_41_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 41) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk20_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk20] at h
  exact h.2

theorem ttFiber30ReverseSingleStep41 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 9) (ttFiber30StateAt 41) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 9) (ttFiber30StateAt 41)
      (ttFiber30RowAt 41).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 41) (by decide) ttFiber30ReverseRow_41_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_42_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 42) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk21] at h
  exact h.1

theorem ttFiber30ReverseSingleStep42 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 10) (ttFiber30StateAt 42) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 10) (ttFiber30StateAt 42)
      (ttFiber30RowAt 42).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 42) (by decide) ttFiber30ReverseRow_42_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_43_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 43) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk21_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk21] at h
  exact h.2

theorem ttFiber30ReverseSingleStep43 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 43) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 43)
      (ttFiber30RowAt 43).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 43) (by decide) ttFiber30ReverseRow_43_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_44_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 44) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk22] at h
  exact h.1

theorem ttFiber30ReverseSingleStep44 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 44) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 44)
      (ttFiber30RowAt 44).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 44) (by decide) ttFiber30ReverseRow_44_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_45_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 45) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk22_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk22] at h
  exact h.2

theorem ttFiber30ReverseSingleStep45 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 41) (ttFiber30StateAt 45) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 41) (ttFiber30StateAt 45)
      (ttFiber30RowAt 45).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 45) (by decide) ttFiber30ReverseRow_45_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_46_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 46) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk23] at h
  exact h.1

theorem ttFiber30ReverseSingleStep46 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 14) (ttFiber30StateAt 46) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 14) (ttFiber30StateAt 46)
      (ttFiber30RowAt 46).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 46) (by decide) ttFiber30ReverseRow_46_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_47_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 47) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk23_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk23] at h
  exact h.2

theorem ttFiber30ReverseSingleStep47 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 15) (ttFiber30StateAt 47) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 15) (ttFiber30StateAt 47)
      (ttFiber30RowAt 47).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 47) (by decide) ttFiber30ReverseRow_47_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_48_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 48) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk24] at h
  exact h.1

theorem ttFiber30ReverseSingleStep48 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 16) (ttFiber30StateAt 48) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 16) (ttFiber30StateAt 48)
      (ttFiber30RowAt 48).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 48) (by decide) ttFiber30ReverseRow_48_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_49_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 49) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk24_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk24] at h
  exact h.2

theorem ttFiber30ReverseSingleStep49 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 17) (ttFiber30StateAt 49) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 17) (ttFiber30StateAt 49)
      (ttFiber30RowAt 49).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 49) (by decide) ttFiber30ReverseRow_49_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_50_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 50) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk25] at h
  exact h.1

theorem ttFiber30ReverseSingleStep50 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 18) (ttFiber30StateAt 50) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 18) (ttFiber30StateAt 50)
      (ttFiber30RowAt 50).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 50) (by decide) ttFiber30ReverseRow_50_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_51_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 51) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk25_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk25] at h
  exact h.2

theorem ttFiber30ReverseSingleStep51 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 19) (ttFiber30StateAt 51) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 19) (ttFiber30StateAt 51)
      (ttFiber30RowAt 51).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 51) (by decide) ttFiber30ReverseRow_51_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_52_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 52) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk26] at h
  exact h.1

theorem ttFiber30ReverseSingleStep52 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 52) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 40) (ttFiber30StateAt 52)
      (ttFiber30RowAt 52).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 52) (by decide) ttFiber30ReverseRow_52_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_53_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 53) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk26_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk26] at h
  exact h.2

theorem ttFiber30ReverseSingleStep53 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 41) (ttFiber30StateAt 53) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 41) (ttFiber30StateAt 53)
      (ttFiber30RowAt 53).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 53) (by decide) ttFiber30ReverseRow_53_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_54_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 54) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk27] at h
  exact h.1

theorem ttFiber30ReverseSingleStep54 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 22) (ttFiber30StateAt 54) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 22) (ttFiber30StateAt 54)
      (ttFiber30RowAt 54).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 54) (by decide) ttFiber30ReverseRow_54_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_55_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 55) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk27_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk27] at h
  exact h.2

theorem ttFiber30ReverseSingleStep55 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 23) (ttFiber30StateAt 55) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 23) (ttFiber30StateAt 55)
      (ttFiber30RowAt 55).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 55) (by decide) ttFiber30ReverseRow_55_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_56_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 56) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk28] at h
  exact h.1

theorem ttFiber30ReverseSingleStep56 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 39) (ttFiber30StateAt 56) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 39) (ttFiber30StateAt 56)
      (ttFiber30RowAt 56).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 56) (by decide) ttFiber30ReverseRow_56_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_57_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 57) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk28_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk28] at h
  exact h.2

theorem ttFiber30ReverseSingleStep57 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 38) (ttFiber30StateAt 57) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 38) (ttFiber30StateAt 57)
      (ttFiber30RowAt 57).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 57) (by decide) ttFiber30ReverseRow_57_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_58_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 58) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk29] at h
  exact h.1

theorem ttFiber30ReverseSingleStep58 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 36) (ttFiber30StateAt 58) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 36) (ttFiber30StateAt 58)
      (ttFiber30RowAt 58).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 58) (by decide) ttFiber30ReverseRow_58_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_59_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 59) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk29_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk29] at h
  exact h.2

theorem ttFiber30ReverseSingleStep59 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 37) (ttFiber30StateAt 59) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 37) (ttFiber30StateAt 59)
      (ttFiber30RowAt 59).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 59) (by decide) ttFiber30ReverseRow_59_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_60_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 60) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk30] at h
  exact h.1

theorem ttFiber30ReverseSingleStep60 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 60) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 32) (ttFiber30StateAt 60)
      (ttFiber30RowAt 60).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 60) (by decide) ttFiber30ReverseRow_60_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_61_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 61) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk30_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk30] at h
  exact h.2

theorem ttFiber30ReverseSingleStep61 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 33) (ttFiber30StateAt 61) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 33) (ttFiber30StateAt 61)
      (ttFiber30RowAt 61).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 61) (by decide) ttFiber30ReverseRow_61_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_62_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 62) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk31] at h
  exact h.1

theorem ttFiber30ReverseSingleStep62 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 34) (ttFiber30StateAt 62) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 34) (ttFiber30StateAt 62)
      (ttFiber30RowAt 62).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 62) (by decide) ttFiber30ReverseRow_62_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30ReverseRow_63_ok' :
    directRowReverseValid ttFiber30Key ttFiber30Expected (ttFiber30RowAt 63) = true := by
  have h := GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk31_ok
  simp [GoertzelLemma818CompositeReverseAudit.ttReverseFiber30Chunk31] at h
  exact h.2

theorem ttFiber30ReverseSingleStep63 :
    chainSingleKempeStep ttWord (ttFiber30StateAt 35) (ttFiber30StateAt 63) = true := by
  apply chainSpecifiedKempeStep_implies_single ttWord (ttFiber30StateAt 35) (ttFiber30StateAt 63)
      (ttFiber30RowAt 63).move
  · decide
  · decide
  · have h := directRowReverseValid_step_of_ne ttFiber30Key ttFiber30Expected
      (ttFiber30RowAt 63) (by decide) ttFiber30ReverseRow_63_ok'
    simpa [ttFiber30StateAt, ttFiber30RowAt, ttFiber30Rows, listGetD, directRow] using h

theorem ttFiber30FirstPassGrows :
    ((chainClosureStep ttWord ttFiber30DirectStates [ttFiber30StateAt 0]).length ==
      [ttFiber30StateAt 0].length) = false := by
  have hroot : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30DirectStates [ttFiber30StateAt 0] :=
    chainClosureStep_mem_of_seen ttWord ttFiber30DirectStates [ttFiber30StateAt 0]
      (ttFiber30StateAt 0) (by simp)
  have hnew : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30DirectStates [ttFiber30StateAt 0] :=
    chainClosureStep_mem_of_seen_step ttWord ttFiber30DirectStates [ttFiber30StateAt 0]
      (ttFiber30StateAt 0) (ttFiber30StateAt 1) (by decide) (by simp)
      ttFiber30ReverseSingleStep1
  simpa using list_length_beq_one_false_of_two_mem
    (chainClosureStep ttWord ttFiber30DirectStates [ttFiber30StateAt 0])
    (ttFiber30StateAt 0) (ttFiber30StateAt 1) hroot hnew (by decide)

theorem ttFiber30State0_in_pass0_full :
    ttFiber30StateAt 0 ∈ [ttFiber30StateAt 0] := by
  simp

theorem ttFiber30State0_in_pass1_full :
    ttFiber30StateAt 0 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  exact chainClosureStep_mem_of_seen ttWord ttFiber30DirectStates
    ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full

theorem ttFiber30State1_in_pass1_prefix1 :
    ttFiber30StateAt 1 ∈ chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix0 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix0
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix1 = ttFiber30Prefix0 ++ [ttFiber30StateAt 1] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 1) []
    (chainClosureStep ttWord ttFiber30Prefix0 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep1

theorem ttFiber30State1_in_pass1_full :
    ttFiber30StateAt 1 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix1 ++ [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1

theorem ttFiber30State2_in_pass1_prefix2 :
    ttFiber30StateAt 2 ∈ chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix1
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix2 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 2) []
    (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep2

theorem ttFiber30State2_in_pass1_full :
    ttFiber30StateAt 2 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix2 ++ [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 2) ttFiber30State2_in_pass1_prefix2

theorem ttFiber30State3_in_pass1_prefix3 :
    ttFiber30StateAt 3 ∈ chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix2 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2]
      (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1
  rw [show ttFiber30Prefix3 = ttFiber30Prefix2 ++ [ttFiber30StateAt 3] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 3) []
    (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) hparentBefore ttFiber30ReverseSingleStep3

theorem ttFiber30State3_in_pass1_full :
    ttFiber30StateAt 3 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix3 ++ [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 3) ttFiber30State3_in_pass1_prefix3

theorem ttFiber30State4_in_pass1_prefix4 :
    ttFiber30StateAt 4 ∈ chainClosureStep ttWord ttFiber30Prefix4 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 2 ∈
      chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix3 = ttFiber30Prefix2 ++ [ttFiber30StateAt 3] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 3]
      (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 2) ttFiber30State2_in_pass1_prefix2
  rw [show ttFiber30Prefix4 = ttFiber30Prefix3 ++ [ttFiber30StateAt 4] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 4) []
    (chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 2) hparentBefore ttFiber30ReverseSingleStep4

theorem ttFiber30State4_in_pass1_full :
    ttFiber30StateAt 4 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix4 ++ [ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix4 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 4) ttFiber30State4_in_pass1_prefix4

theorem ttFiber30State6_in_pass1_prefix6 :
    ttFiber30StateAt 6 ∈ chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30Prefix5 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix5 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5]
      (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1
  rw [show ttFiber30Prefix6 = ttFiber30Prefix5 ++ [ttFiber30StateAt 6] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 6) []
    (chainClosureStep ttWord ttFiber30Prefix5 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) hparentBefore ttFiber30ReverseSingleStep6

theorem ttFiber30State6_in_pass1_full :
    ttFiber30StateAt 6 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix6 ++ [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 6) ttFiber30State6_in_pass1_prefix6

theorem ttFiber30State7_in_pass1_prefix7 :
    ttFiber30StateAt 7 ∈ chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix6
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix7 = ttFiber30Prefix6 ++ [ttFiber30StateAt 7] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 7) []
    (chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep7

theorem ttFiber30State7_in_pass1_full :
    ttFiber30StateAt 7 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix7 ++ [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 7) ttFiber30State7_in_pass1_prefix7

theorem ttFiber30State8_in_pass1_prefix8 :
    ttFiber30StateAt 8 ∈ chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix7
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix8 = ttFiber30Prefix7 ++ [ttFiber30StateAt 8] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 8) []
    (chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep8

theorem ttFiber30State8_in_pass1_full :
    ttFiber30StateAt 8 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix8 ++ [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 8) ttFiber30State8_in_pass1_prefix8

theorem ttFiber30State9_in_pass1_prefix9 :
    ttFiber30StateAt 9 ∈ chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix8 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8]
      (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1
  rw [show ttFiber30Prefix9 = ttFiber30Prefix8 ++ [ttFiber30StateAt 9] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 9) []
    (chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) hparentBefore ttFiber30ReverseSingleStep9

theorem ttFiber30State9_in_pass1_full :
    ttFiber30StateAt 9 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix9 ++ [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 9) ttFiber30State9_in_pass1_prefix9

theorem ttFiber30State10_in_pass1_prefix10 :
    ttFiber30StateAt 10 ∈ chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 2 ∈
      chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix9 = ttFiber30Prefix2 ++ [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9]
      (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 2) ttFiber30State2_in_pass1_prefix2
  rw [show ttFiber30Prefix10 = ttFiber30Prefix9 ++ [ttFiber30StateAt 10] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 10) []
    (chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 2) hparentBefore ttFiber30ReverseSingleStep10

theorem ttFiber30State10_in_pass1_full :
    ttFiber30StateAt 10 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix10 ++ [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 10) ttFiber30State10_in_pass1_prefix10

theorem ttFiber30State11_in_pass1_prefix11 :
    ttFiber30StateAt 11 ∈ chainClosureStep ttWord ttFiber30Prefix11 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 3 ∈
      chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix10 = ttFiber30Prefix3 ++ [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10]
      (chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 3) ttFiber30State3_in_pass1_prefix3
  rw [show ttFiber30Prefix11 = ttFiber30Prefix10 ++ [ttFiber30StateAt 11] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 11) []
    (chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 3) hparentBefore ttFiber30ReverseSingleStep11

theorem ttFiber30State11_in_pass1_full :
    ttFiber30StateAt 11 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix11 ++ [ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix11 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 11) ttFiber30State11_in_pass1_prefix11

theorem ttFiber30State12_in_pass1_prefix12 :
    ttFiber30StateAt 12 ∈ chainClosureStep ttWord ttFiber30Prefix12 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 4 ∈
      chainClosureStep ttWord ttFiber30Prefix11 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix11 = ttFiber30Prefix4 ++ [ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11]
      (chainClosureStep ttWord ttFiber30Prefix4 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 4) ttFiber30State4_in_pass1_prefix4
  rw [show ttFiber30Prefix12 = ttFiber30Prefix11 ++ [ttFiber30StateAt 12] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 12) []
    (chainClosureStep ttWord ttFiber30Prefix11 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 4) hparentBefore ttFiber30ReverseSingleStep12

theorem ttFiber30State12_in_pass1_full :
    ttFiber30StateAt 12 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix12 ++ [ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix12 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 12) ttFiber30State12_in_pass1_prefix12

theorem ttFiber30State14_in_pass1_prefix14 :
    ttFiber30StateAt 14 ∈ chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 6 ∈
      chainClosureStep ttWord ttFiber30Prefix13 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix13 = ttFiber30Prefix6 ++ [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13]
      (chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 6) ttFiber30State6_in_pass1_prefix6
  rw [show ttFiber30Prefix14 = ttFiber30Prefix13 ++ [ttFiber30StateAt 14] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 14) []
    (chainClosureStep ttWord ttFiber30Prefix13 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 6) hparentBefore ttFiber30ReverseSingleStep14

theorem ttFiber30State14_in_pass1_full :
    ttFiber30StateAt 14 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix14 ++ [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 14) ttFiber30State14_in_pass1_prefix14

theorem ttFiber30State15_in_pass1_prefix15 :
    ttFiber30StateAt 15 ∈ chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 7 ∈
      chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix14 = ttFiber30Prefix7 ++ [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14]
      (chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 7) ttFiber30State7_in_pass1_prefix7
  rw [show ttFiber30Prefix15 = ttFiber30Prefix14 ++ [ttFiber30StateAt 15] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 15) []
    (chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 7) hparentBefore ttFiber30ReverseSingleStep15

theorem ttFiber30State15_in_pass1_full :
    ttFiber30StateAt 15 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix15 ++ [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 15) ttFiber30State15_in_pass1_prefix15

theorem ttFiber30State16_in_pass1_prefix16 :
    ttFiber30StateAt 16 ∈ chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix15
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix16 = ttFiber30Prefix15 ++ [ttFiber30StateAt 16] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 16) []
    (chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep16

theorem ttFiber30State16_in_pass1_full :
    ttFiber30StateAt 16 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix16 ++ [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 16) ttFiber30State16_in_pass1_prefix16

theorem ttFiber30State17_in_pass1_prefix17 :
    ttFiber30StateAt 17 ∈ chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix16 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16]
      (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1
  rw [show ttFiber30Prefix17 = ttFiber30Prefix16 ++ [ttFiber30StateAt 17] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 17) []
    (chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) hparentBefore ttFiber30ReverseSingleStep17

theorem ttFiber30State17_in_pass1_full :
    ttFiber30StateAt 17 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix17 ++ [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 17) ttFiber30State17_in_pass1_prefix17

theorem ttFiber30State18_in_pass1_prefix18 :
    ttFiber30StateAt 18 ∈ chainClosureStep ttWord ttFiber30Prefix18 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 2 ∈
      chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix17 = ttFiber30Prefix2 ++ [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17]
      (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 2) ttFiber30State2_in_pass1_prefix2
  rw [show ttFiber30Prefix18 = ttFiber30Prefix17 ++ [ttFiber30StateAt 18] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 18) []
    (chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 2) hparentBefore ttFiber30ReverseSingleStep18

theorem ttFiber30State18_in_pass1_full :
    ttFiber30StateAt 18 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix18 ++ [ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix18 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 18) ttFiber30State18_in_pass1_prefix18

theorem ttFiber30State19_in_pass1_prefix19 :
    ttFiber30StateAt 19 ∈ chainClosureStep ttWord ttFiber30Prefix19 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 3 ∈
      chainClosureStep ttWord ttFiber30Prefix18 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix18 = ttFiber30Prefix3 ++ [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18]
      (chainClosureStep ttWord ttFiber30Prefix3 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 3) ttFiber30State3_in_pass1_prefix3
  rw [show ttFiber30Prefix19 = ttFiber30Prefix18 ++ [ttFiber30StateAt 19] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 19) []
    (chainClosureStep ttWord ttFiber30Prefix18 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 3) hparentBefore ttFiber30ReverseSingleStep19

theorem ttFiber30State19_in_pass1_full :
    ttFiber30StateAt 19 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix19 ++ [ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix19 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 19) ttFiber30State19_in_pass1_prefix19

theorem ttFiber30State20_in_pass1_prefix20 :
    ttFiber30StateAt 20 ∈ chainClosureStep ttWord ttFiber30Prefix20 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 16 ∈
      chainClosureStep ttWord ttFiber30Prefix19 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix19 = ttFiber30Prefix16 ++ [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19]
      (chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 16) ttFiber30State16_in_pass1_prefix16
  rw [show ttFiber30Prefix20 = ttFiber30Prefix19 ++ [ttFiber30StateAt 20] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 20) []
    (chainClosureStep ttWord ttFiber30Prefix19 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 16) hparentBefore ttFiber30ReverseSingleStep20

theorem ttFiber30State20_in_pass1_full :
    ttFiber30StateAt 20 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix20 ++ [ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix20 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 20) ttFiber30State20_in_pass1_prefix20

theorem ttFiber30State21_in_pass1_prefix21 :
    ttFiber30StateAt 21 ∈ chainClosureStep ttWord ttFiber30Prefix21 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 17 ∈
      chainClosureStep ttWord ttFiber30Prefix20 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix20 = ttFiber30Prefix17 ++ [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20]
      (chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 17) ttFiber30State17_in_pass1_prefix17
  rw [show ttFiber30Prefix21 = ttFiber30Prefix20 ++ [ttFiber30StateAt 21] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 21) []
    (chainClosureStep ttWord ttFiber30Prefix20 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 17) hparentBefore ttFiber30ReverseSingleStep21

theorem ttFiber30State21_in_pass1_full :
    ttFiber30StateAt 21 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix21 ++ [ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix21 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 21) ttFiber30State21_in_pass1_prefix21

theorem ttFiber30State22_in_pass1_prefix22 :
    ttFiber30StateAt 22 ∈ chainClosureStep ttWord ttFiber30Prefix22 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 6 ∈
      chainClosureStep ttWord ttFiber30Prefix21 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix21 = ttFiber30Prefix6 ++ [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21]
      (chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 6) ttFiber30State6_in_pass1_prefix6
  rw [show ttFiber30Prefix22 = ttFiber30Prefix21 ++ [ttFiber30StateAt 22] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 22) []
    (chainClosureStep ttWord ttFiber30Prefix21 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 6) hparentBefore ttFiber30ReverseSingleStep22

theorem ttFiber30State22_in_pass1_full :
    ttFiber30StateAt 22 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix22 ++ [ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix22 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 22) ttFiber30State22_in_pass1_prefix22

theorem ttFiber30State23_in_pass1_prefix23 :
    ttFiber30StateAt 23 ∈ chainClosureStep ttWord ttFiber30Prefix23 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 7 ∈
      chainClosureStep ttWord ttFiber30Prefix22 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix22 = ttFiber30Prefix7 ++ [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22]
      (chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 7) ttFiber30State7_in_pass1_prefix7
  rw [show ttFiber30Prefix23 = ttFiber30Prefix22 ++ [ttFiber30StateAt 23] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 23) []
    (chainClosureStep ttWord ttFiber30Prefix22 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 7) hparentBefore ttFiber30ReverseSingleStep23

theorem ttFiber30State23_in_pass1_full :
    ttFiber30StateAt 23 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix23 ++ [ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix23 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 23) ttFiber30State23_in_pass1_prefix23

theorem ttFiber30State24_in_pass1_prefix24 :
    ttFiber30StateAt 24 ∈ chainClosureStep ttWord ttFiber30Prefix24 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 8 ∈
      chainClosureStep ttWord ttFiber30Prefix23 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix23 = ttFiber30Prefix8 ++ [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23]
      (chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 8) ttFiber30State8_in_pass1_prefix8
  rw [show ttFiber30Prefix24 = ttFiber30Prefix23 ++ [ttFiber30StateAt 24] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 24) []
    (chainClosureStep ttWord ttFiber30Prefix23 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 8) hparentBefore ttFiber30ReverseSingleStep24

theorem ttFiber30State24_in_pass1_full :
    ttFiber30StateAt 24 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix24 ++ [ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix24 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 24) ttFiber30State24_in_pass1_prefix24

theorem ttFiber30State25_in_pass1_prefix25 :
    ttFiber30StateAt 25 ∈ chainClosureStep ttWord ttFiber30Prefix25 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 9 ∈
      chainClosureStep ttWord ttFiber30Prefix24 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix24 = ttFiber30Prefix9 ++ [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24]
      (chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 9) ttFiber30State9_in_pass1_prefix9
  rw [show ttFiber30Prefix25 = ttFiber30Prefix24 ++ [ttFiber30StateAt 25] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 25) []
    (chainClosureStep ttWord ttFiber30Prefix24 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 9) hparentBefore ttFiber30ReverseSingleStep25

theorem ttFiber30State25_in_pass1_full :
    ttFiber30StateAt 25 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix25 ++ [ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix25 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 25) ttFiber30State25_in_pass1_prefix25

theorem ttFiber30State26_in_pass1_prefix26 :
    ttFiber30StateAt 26 ∈ chainClosureStep ttWord ttFiber30Prefix26 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 10 ∈
      chainClosureStep ttWord ttFiber30Prefix25 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix25 = ttFiber30Prefix10 ++ [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25]
      (chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 10) ttFiber30State10_in_pass1_prefix10
  rw [show ttFiber30Prefix26 = ttFiber30Prefix25 ++ [ttFiber30StateAt 26] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 26) []
    (chainClosureStep ttWord ttFiber30Prefix25 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 10) hparentBefore ttFiber30ReverseSingleStep26

theorem ttFiber30State26_in_pass1_full :
    ttFiber30StateAt 26 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix26 ++ [ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix26 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 26) ttFiber30State26_in_pass1_prefix26

theorem ttFiber30State27_in_pass1_prefix27 :
    ttFiber30StateAt 27 ∈ chainClosureStep ttWord ttFiber30Prefix27 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 11 ∈
      chainClosureStep ttWord ttFiber30Prefix26 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix26 = ttFiber30Prefix11 ++ [ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26]
      (chainClosureStep ttWord ttFiber30Prefix11 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 11) ttFiber30State11_in_pass1_prefix11
  rw [show ttFiber30Prefix27 = ttFiber30Prefix26 ++ [ttFiber30StateAt 27] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 27) []
    (chainClosureStep ttWord ttFiber30Prefix26 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 11) hparentBefore ttFiber30ReverseSingleStep27

theorem ttFiber30State27_in_pass1_full :
    ttFiber30StateAt 27 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix27 ++ [ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix27 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 27) ttFiber30State27_in_pass1_prefix27

theorem ttFiber30State28_in_pass1_prefix28 :
    ttFiber30StateAt 28 ∈ chainClosureStep ttWord ttFiber30Prefix28 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 24 ∈
      chainClosureStep ttWord ttFiber30Prefix27 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix27 = ttFiber30Prefix24 ++ [ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27]
      (chainClosureStep ttWord ttFiber30Prefix24 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 24) ttFiber30State24_in_pass1_prefix24
  rw [show ttFiber30Prefix28 = ttFiber30Prefix27 ++ [ttFiber30StateAt 28] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 28) []
    (chainClosureStep ttWord ttFiber30Prefix27 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 24) hparentBefore ttFiber30ReverseSingleStep28

theorem ttFiber30State28_in_pass1_full :
    ttFiber30StateAt 28 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix28 ++ [ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix28 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 28) ttFiber30State28_in_pass1_prefix28

theorem ttFiber30State29_in_pass1_prefix29 :
    ttFiber30StateAt 29 ∈ chainClosureStep ttWord ttFiber30Prefix29 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 25 ∈
      chainClosureStep ttWord ttFiber30Prefix28 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix28 = ttFiber30Prefix25 ++ [ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28]
      (chainClosureStep ttWord ttFiber30Prefix25 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 25) ttFiber30State25_in_pass1_prefix25
  rw [show ttFiber30Prefix29 = ttFiber30Prefix28 ++ [ttFiber30StateAt 29] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 29) []
    (chainClosureStep ttWord ttFiber30Prefix28 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 25) hparentBefore ttFiber30ReverseSingleStep29

theorem ttFiber30State29_in_pass1_full :
    ttFiber30StateAt 29 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix29 ++ [ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix29 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 29) ttFiber30State29_in_pass1_prefix29

theorem ttFiber30State30_in_pass1_prefix30 :
    ttFiber30StateAt 30 ∈ chainClosureStep ttWord ttFiber30Prefix30 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 14 ∈
      chainClosureStep ttWord ttFiber30Prefix29 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix29 = ttFiber30Prefix14 ++ [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29]
      (chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 14) ttFiber30State14_in_pass1_prefix14
  rw [show ttFiber30Prefix30 = ttFiber30Prefix29 ++ [ttFiber30StateAt 30] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 30) []
    (chainClosureStep ttWord ttFiber30Prefix29 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 14) hparentBefore ttFiber30ReverseSingleStep30

theorem ttFiber30State30_in_pass1_full :
    ttFiber30StateAt 30 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix30 ++ [ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix30 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 30) ttFiber30State30_in_pass1_prefix30

theorem ttFiber30State31_in_pass1_prefix31 :
    ttFiber30StateAt 31 ∈ chainClosureStep ttWord ttFiber30Prefix31 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 15 ∈
      chainClosureStep ttWord ttFiber30Prefix30 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix30 = ttFiber30Prefix15 ++ [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30]
      (chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 15) ttFiber30State15_in_pass1_prefix15
  rw [show ttFiber30Prefix31 = ttFiber30Prefix30 ++ [ttFiber30StateAt 31] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 31) []
    (chainClosureStep ttWord ttFiber30Prefix30 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 15) hparentBefore ttFiber30ReverseSingleStep31

theorem ttFiber30State31_in_pass1_full :
    ttFiber30StateAt 31 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix31 ++ [ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix31 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 31) ttFiber30State31_in_pass1_prefix31

theorem ttFiber30State32_in_pass1_prefix32 :
    ttFiber30StateAt 32 ∈ chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 0 ∈
      chainClosureStep ttWord ttFiber30Prefix31 ([ttFiber30StateAt 0]) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix31
      ([ttFiber30StateAt 0]) (ttFiber30StateAt 0) ttFiber30State0_in_pass0_full
  rw [show ttFiber30Prefix32 = ttFiber30Prefix31 ++ [ttFiber30StateAt 32] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 32) []
    (chainClosureStep ttWord ttFiber30Prefix31 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 0) hparentBefore ttFiber30ReverseSingleStep32

theorem ttFiber30State32_in_pass1_full :
    ttFiber30StateAt 32 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix32 ++ [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 32) ttFiber30State32_in_pass1_prefix32

theorem ttFiber30State33_in_pass1_prefix33 :
    ttFiber30StateAt 33 ∈ chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 1 ∈
      chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix32 = ttFiber30Prefix1 ++ [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 2, ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32]
      (chainClosureStep ttWord ttFiber30Prefix1 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 1) ttFiber30State1_in_pass1_prefix1
  rw [show ttFiber30Prefix33 = ttFiber30Prefix32 ++ [ttFiber30StateAt 33] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 33) []
    (chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 1) hparentBefore ttFiber30ReverseSingleStep33

theorem ttFiber30State33_in_pass1_full :
    ttFiber30StateAt 33 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix33 ++ [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 33) ttFiber30State33_in_pass1_prefix33

theorem ttFiber30State34_in_pass1_prefix34 :
    ttFiber30StateAt 34 ∈ chainClosureStep ttWord ttFiber30Prefix34 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 2 ∈
      chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix33 = ttFiber30Prefix2 ++ [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 3, ttFiber30StateAt 4, ttFiber30StateAt 5, ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33]
      (chainClosureStep ttWord ttFiber30Prefix2 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 2) ttFiber30State2_in_pass1_prefix2
  rw [show ttFiber30Prefix34 = ttFiber30Prefix33 ++ [ttFiber30StateAt 34] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 34) []
    (chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 2) hparentBefore ttFiber30ReverseSingleStep34

theorem ttFiber30State34_in_pass1_full :
    ttFiber30StateAt 34 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix34 ++ [ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix34 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 34) ttFiber30State34_in_pass1_prefix34

theorem ttFiber30State35_in_pass1_prefix35 :
    ttFiber30StateAt 35 ∈ chainClosureStep ttWord ttFiber30Prefix35 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 32 ∈
      chainClosureStep ttWord ttFiber30Prefix34 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix34 = ttFiber30Prefix32 ++ [ttFiber30StateAt 33, ttFiber30StateAt 34] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 33, ttFiber30StateAt 34]
      (chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 32) ttFiber30State32_in_pass1_prefix32
  rw [show ttFiber30Prefix35 = ttFiber30Prefix34 ++ [ttFiber30StateAt 35] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 35) []
    (chainClosureStep ttWord ttFiber30Prefix34 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 32) hparentBefore ttFiber30ReverseSingleStep35

theorem ttFiber30State35_in_pass1_full :
    ttFiber30StateAt 35 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix35 ++ [ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix35 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 35) ttFiber30State35_in_pass1_prefix35

theorem ttFiber30State36_in_pass1_prefix36 :
    ttFiber30StateAt 36 ∈ chainClosureStep ttWord ttFiber30Prefix36 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 32 ∈
      chainClosureStep ttWord ttFiber30Prefix35 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix35 = ttFiber30Prefix32 ++ [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35]
      (chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 32) ttFiber30State32_in_pass1_prefix32
  rw [show ttFiber30Prefix36 = ttFiber30Prefix35 ++ [ttFiber30StateAt 36] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 36) []
    (chainClosureStep ttWord ttFiber30Prefix35 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 32) hparentBefore ttFiber30ReverseSingleStep36

theorem ttFiber30State36_in_pass1_full :
    ttFiber30StateAt 36 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix36 ++ [ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix36 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 36) ttFiber30State36_in_pass1_prefix36

theorem ttFiber30State37_in_pass1_prefix37 :
    ttFiber30StateAt 37 ∈ chainClosureStep ttWord ttFiber30Prefix37 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 33 ∈
      chainClosureStep ttWord ttFiber30Prefix36 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix36 = ttFiber30Prefix33 ++ [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36]
      (chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 33) ttFiber30State33_in_pass1_prefix33
  rw [show ttFiber30Prefix37 = ttFiber30Prefix36 ++ [ttFiber30StateAt 37] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 37) []
    (chainClosureStep ttWord ttFiber30Prefix36 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 33) hparentBefore ttFiber30ReverseSingleStep37

theorem ttFiber30State37_in_pass1_full :
    ttFiber30StateAt 37 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix37 ++ [ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix37 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 37) ttFiber30State37_in_pass1_prefix37

theorem ttFiber30State38_in_pass1_prefix38 :
    ttFiber30StateAt 38 ∈ chainClosureStep ttWord ttFiber30Prefix38 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 6 ∈
      chainClosureStep ttWord ttFiber30Prefix37 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix37 = ttFiber30Prefix6 ++ [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37]
      (chainClosureStep ttWord ttFiber30Prefix6 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 6) ttFiber30State6_in_pass1_prefix6
  rw [show ttFiber30Prefix38 = ttFiber30Prefix37 ++ [ttFiber30StateAt 38] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 38) []
    (chainClosureStep ttWord ttFiber30Prefix37 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 6) hparentBefore ttFiber30ReverseSingleStep38

theorem ttFiber30State38_in_pass1_full :
    ttFiber30StateAt 38 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix38 ++ [ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix38 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 38) ttFiber30State38_in_pass1_prefix38

theorem ttFiber30State39_in_pass1_prefix39 :
    ttFiber30StateAt 39 ∈ chainClosureStep ttWord ttFiber30Prefix39 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 7 ∈
      chainClosureStep ttWord ttFiber30Prefix38 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix38 = ttFiber30Prefix7 ++ [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38]
      (chainClosureStep ttWord ttFiber30Prefix7 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 7) ttFiber30State7_in_pass1_prefix7
  rw [show ttFiber30Prefix39 = ttFiber30Prefix38 ++ [ttFiber30StateAt 39] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 39) []
    (chainClosureStep ttWord ttFiber30Prefix38 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 7) hparentBefore ttFiber30ReverseSingleStep39

theorem ttFiber30State39_in_pass1_full :
    ttFiber30StateAt 39 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix39 ++ [ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix39 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 39) ttFiber30State39_in_pass1_prefix39

theorem ttFiber30State40_in_pass1_prefix40 :
    ttFiber30StateAt 40 ∈ chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 8 ∈
      chainClosureStep ttWord ttFiber30Prefix39 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix39 = ttFiber30Prefix8 ++ [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39]
      (chainClosureStep ttWord ttFiber30Prefix8 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 8) ttFiber30State8_in_pass1_prefix8
  rw [show ttFiber30Prefix40 = ttFiber30Prefix39 ++ [ttFiber30StateAt 40] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 40) []
    (chainClosureStep ttWord ttFiber30Prefix39 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 8) hparentBefore ttFiber30ReverseSingleStep40

theorem ttFiber30State40_in_pass1_full :
    ttFiber30StateAt 40 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix40 ++ [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 40) ttFiber30State40_in_pass1_prefix40

theorem ttFiber30State41_in_pass1_prefix41 :
    ttFiber30StateAt 41 ∈ chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 9 ∈
      chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix40 = ttFiber30Prefix9 ++ [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40]
      (chainClosureStep ttWord ttFiber30Prefix9 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 9) ttFiber30State9_in_pass1_prefix9
  rw [show ttFiber30Prefix41 = ttFiber30Prefix40 ++ [ttFiber30StateAt 41] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 41) []
    (chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 9) hparentBefore ttFiber30ReverseSingleStep41

theorem ttFiber30State41_in_pass1_full :
    ttFiber30StateAt 41 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix41 ++ [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 41) ttFiber30State41_in_pass1_prefix41

theorem ttFiber30State42_in_pass1_prefix42 :
    ttFiber30StateAt 42 ∈ chainClosureStep ttWord ttFiber30Prefix42 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 10 ∈
      chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix41 = ttFiber30Prefix10 ++ [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41]
      (chainClosureStep ttWord ttFiber30Prefix10 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 10) ttFiber30State10_in_pass1_prefix10
  rw [show ttFiber30Prefix42 = ttFiber30Prefix41 ++ [ttFiber30StateAt 42] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 42) []
    (chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 10) hparentBefore ttFiber30ReverseSingleStep42

theorem ttFiber30State42_in_pass1_full :
    ttFiber30StateAt 42 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix42 ++ [ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix42 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 42) ttFiber30State42_in_pass1_prefix42

theorem ttFiber30State43_in_pass1_prefix43 :
    ttFiber30StateAt 43 ∈ chainClosureStep ttWord ttFiber30Prefix43 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 40 ∈
      chainClosureStep ttWord ttFiber30Prefix42 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix42 = ttFiber30Prefix40 ++ [ttFiber30StateAt 41, ttFiber30StateAt 42] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 41, ttFiber30StateAt 42]
      (chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 40) ttFiber30State40_in_pass1_prefix40
  rw [show ttFiber30Prefix43 = ttFiber30Prefix42 ++ [ttFiber30StateAt 43] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 43) []
    (chainClosureStep ttWord ttFiber30Prefix42 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 40) hparentBefore ttFiber30ReverseSingleStep43

theorem ttFiber30State43_in_pass1_full :
    ttFiber30StateAt 43 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix43 ++ [ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix43 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 43) ttFiber30State43_in_pass1_prefix43

theorem ttFiber30State44_in_pass1_prefix44 :
    ttFiber30StateAt 44 ∈ chainClosureStep ttWord ttFiber30Prefix44 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 40 ∈
      chainClosureStep ttWord ttFiber30Prefix43 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix43 = ttFiber30Prefix40 ++ [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43]
      (chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 40) ttFiber30State40_in_pass1_prefix40
  rw [show ttFiber30Prefix44 = ttFiber30Prefix43 ++ [ttFiber30StateAt 44] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 44) []
    (chainClosureStep ttWord ttFiber30Prefix43 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 40) hparentBefore ttFiber30ReverseSingleStep44

theorem ttFiber30State44_in_pass1_full :
    ttFiber30StateAt 44 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix44 ++ [ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix44 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 44) ttFiber30State44_in_pass1_prefix44

theorem ttFiber30State45_in_pass1_prefix45 :
    ttFiber30StateAt 45 ∈ chainClosureStep ttWord ttFiber30Prefix45 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 41 ∈
      chainClosureStep ttWord ttFiber30Prefix44 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix44 = ttFiber30Prefix41 ++ [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44]
      (chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 41) ttFiber30State41_in_pass1_prefix41
  rw [show ttFiber30Prefix45 = ttFiber30Prefix44 ++ [ttFiber30StateAt 45] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 45) []
    (chainClosureStep ttWord ttFiber30Prefix44 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 41) hparentBefore ttFiber30ReverseSingleStep45

theorem ttFiber30State45_in_pass1_full :
    ttFiber30StateAt 45 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix45 ++ [ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix45 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 45) ttFiber30State45_in_pass1_prefix45

theorem ttFiber30State46_in_pass1_prefix46 :
    ttFiber30StateAt 46 ∈ chainClosureStep ttWord ttFiber30Prefix46 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 14 ∈
      chainClosureStep ttWord ttFiber30Prefix45 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix45 = ttFiber30Prefix14 ++ [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45]
      (chainClosureStep ttWord ttFiber30Prefix14 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 14) ttFiber30State14_in_pass1_prefix14
  rw [show ttFiber30Prefix46 = ttFiber30Prefix45 ++ [ttFiber30StateAt 46] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 46) []
    (chainClosureStep ttWord ttFiber30Prefix45 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 14) hparentBefore ttFiber30ReverseSingleStep46

theorem ttFiber30State46_in_pass1_full :
    ttFiber30StateAt 46 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix46 ++ [ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix46 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 46) ttFiber30State46_in_pass1_prefix46

theorem ttFiber30State47_in_pass1_prefix47 :
    ttFiber30StateAt 47 ∈ chainClosureStep ttWord ttFiber30Prefix47 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 15 ∈
      chainClosureStep ttWord ttFiber30Prefix46 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix46 = ttFiber30Prefix15 ++ [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46]
      (chainClosureStep ttWord ttFiber30Prefix15 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 15) ttFiber30State15_in_pass1_prefix15
  rw [show ttFiber30Prefix47 = ttFiber30Prefix46 ++ [ttFiber30StateAt 47] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 47) []
    (chainClosureStep ttWord ttFiber30Prefix46 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 15) hparentBefore ttFiber30ReverseSingleStep47

theorem ttFiber30State47_in_pass1_full :
    ttFiber30StateAt 47 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix47 ++ [ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix47 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 47) ttFiber30State47_in_pass1_prefix47

theorem ttFiber30State48_in_pass1_prefix48 :
    ttFiber30StateAt 48 ∈ chainClosureStep ttWord ttFiber30Prefix48 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 16 ∈
      chainClosureStep ttWord ttFiber30Prefix47 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix47 = ttFiber30Prefix16 ++ [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47]
      (chainClosureStep ttWord ttFiber30Prefix16 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 16) ttFiber30State16_in_pass1_prefix16
  rw [show ttFiber30Prefix48 = ttFiber30Prefix47 ++ [ttFiber30StateAt 48] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 48) []
    (chainClosureStep ttWord ttFiber30Prefix47 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 16) hparentBefore ttFiber30ReverseSingleStep48

theorem ttFiber30State48_in_pass1_full :
    ttFiber30StateAt 48 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix48 ++ [ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix48 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 48) ttFiber30State48_in_pass1_prefix48

theorem ttFiber30State49_in_pass1_prefix49 :
    ttFiber30StateAt 49 ∈ chainClosureStep ttWord ttFiber30Prefix49 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 17 ∈
      chainClosureStep ttWord ttFiber30Prefix48 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix48 = ttFiber30Prefix17 ++ [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48]
      (chainClosureStep ttWord ttFiber30Prefix17 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 17) ttFiber30State17_in_pass1_prefix17
  rw [show ttFiber30Prefix49 = ttFiber30Prefix48 ++ [ttFiber30StateAt 49] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 49) []
    (chainClosureStep ttWord ttFiber30Prefix48 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 17) hparentBefore ttFiber30ReverseSingleStep49

theorem ttFiber30State49_in_pass1_full :
    ttFiber30StateAt 49 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix49 ++ [ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix49 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 49) ttFiber30State49_in_pass1_prefix49

theorem ttFiber30State50_in_pass1_prefix50 :
    ttFiber30StateAt 50 ∈ chainClosureStep ttWord ttFiber30Prefix50 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 18 ∈
      chainClosureStep ttWord ttFiber30Prefix49 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix49 = ttFiber30Prefix18 ++ [ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49]
      (chainClosureStep ttWord ttFiber30Prefix18 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 18) ttFiber30State18_in_pass1_prefix18
  rw [show ttFiber30Prefix50 = ttFiber30Prefix49 ++ [ttFiber30StateAt 50] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 50) []
    (chainClosureStep ttWord ttFiber30Prefix49 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 18) hparentBefore ttFiber30ReverseSingleStep50

theorem ttFiber30State50_in_pass1_full :
    ttFiber30StateAt 50 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix50 ++ [ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix50 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 50) ttFiber30State50_in_pass1_prefix50

theorem ttFiber30State51_in_pass1_prefix51 :
    ttFiber30StateAt 51 ∈ chainClosureStep ttWord ttFiber30Prefix51 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 19 ∈
      chainClosureStep ttWord ttFiber30Prefix50 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix50 = ttFiber30Prefix19 ++ [ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50]
      (chainClosureStep ttWord ttFiber30Prefix19 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 19) ttFiber30State19_in_pass1_prefix19
  rw [show ttFiber30Prefix51 = ttFiber30Prefix50 ++ [ttFiber30StateAt 51] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 51) []
    (chainClosureStep ttWord ttFiber30Prefix50 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 19) hparentBefore ttFiber30ReverseSingleStep51

theorem ttFiber30State51_in_pass1_full :
    ttFiber30StateAt 51 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix51 ++ [ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix51 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 51) ttFiber30State51_in_pass1_prefix51

theorem ttFiber30State52_in_pass1_prefix52 :
    ttFiber30StateAt 52 ∈ chainClosureStep ttWord ttFiber30Prefix52 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 40 ∈
      chainClosureStep ttWord ttFiber30Prefix51 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix51 = ttFiber30Prefix40 ++ [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51]
      (chainClosureStep ttWord ttFiber30Prefix40 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 40) ttFiber30State40_in_pass1_prefix40
  rw [show ttFiber30Prefix52 = ttFiber30Prefix51 ++ [ttFiber30StateAt 52] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 52) []
    (chainClosureStep ttWord ttFiber30Prefix51 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 40) hparentBefore ttFiber30ReverseSingleStep52

theorem ttFiber30State52_in_pass1_full :
    ttFiber30StateAt 52 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix52 ++ [ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix52 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 52) ttFiber30State52_in_pass1_prefix52

theorem ttFiber30State53_in_pass1_prefix53 :
    ttFiber30StateAt 53 ∈ chainClosureStep ttWord ttFiber30Prefix53 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 41 ∈
      chainClosureStep ttWord ttFiber30Prefix52 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix52 = ttFiber30Prefix41 ++ [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52]
      (chainClosureStep ttWord ttFiber30Prefix41 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 41) ttFiber30State41_in_pass1_prefix41
  rw [show ttFiber30Prefix53 = ttFiber30Prefix52 ++ [ttFiber30StateAt 53] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 53) []
    (chainClosureStep ttWord ttFiber30Prefix52 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 41) hparentBefore ttFiber30ReverseSingleStep53

theorem ttFiber30State53_in_pass1_full :
    ttFiber30StateAt 53 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix53 ++ [ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix53 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 53) ttFiber30State53_in_pass1_prefix53

theorem ttFiber30State54_in_pass1_prefix54 :
    ttFiber30StateAt 54 ∈ chainClosureStep ttWord ttFiber30Prefix54 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 22 ∈
      chainClosureStep ttWord ttFiber30Prefix53 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix53 = ttFiber30Prefix22 ++ [ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53]
      (chainClosureStep ttWord ttFiber30Prefix22 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 22) ttFiber30State22_in_pass1_prefix22
  rw [show ttFiber30Prefix54 = ttFiber30Prefix53 ++ [ttFiber30StateAt 54] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 54) []
    (chainClosureStep ttWord ttFiber30Prefix53 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 22) hparentBefore ttFiber30ReverseSingleStep54

theorem ttFiber30State54_in_pass1_full :
    ttFiber30StateAt 54 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix54 ++ [ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix54 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 54) ttFiber30State54_in_pass1_prefix54

theorem ttFiber30State55_in_pass1_prefix55 :
    ttFiber30StateAt 55 ∈ chainClosureStep ttWord ttFiber30Prefix55 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 23 ∈
      chainClosureStep ttWord ttFiber30Prefix54 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix54 = ttFiber30Prefix23 ++ [ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54]
      (chainClosureStep ttWord ttFiber30Prefix23 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 23) ttFiber30State23_in_pass1_prefix23
  rw [show ttFiber30Prefix55 = ttFiber30Prefix54 ++ [ttFiber30StateAt 55] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 55) []
    (chainClosureStep ttWord ttFiber30Prefix54 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 23) hparentBefore ttFiber30ReverseSingleStep55

theorem ttFiber30State55_in_pass1_full :
    ttFiber30StateAt 55 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix55 ++ [ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix55 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 55) ttFiber30State55_in_pass1_prefix55

theorem ttFiber30State56_in_pass1_prefix56 :
    ttFiber30StateAt 56 ∈ chainClosureStep ttWord ttFiber30Prefix56 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 39 ∈
      chainClosureStep ttWord ttFiber30Prefix55 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix55 = ttFiber30Prefix39 ++ [ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55]
      (chainClosureStep ttWord ttFiber30Prefix39 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 39) ttFiber30State39_in_pass1_prefix39
  rw [show ttFiber30Prefix56 = ttFiber30Prefix55 ++ [ttFiber30StateAt 56] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 56) []
    (chainClosureStep ttWord ttFiber30Prefix55 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 39) hparentBefore ttFiber30ReverseSingleStep56

theorem ttFiber30State56_in_pass1_full :
    ttFiber30StateAt 56 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix56 ++ [ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix56 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 56) ttFiber30State56_in_pass1_prefix56

theorem ttFiber30State57_in_pass1_prefix57 :
    ttFiber30StateAt 57 ∈ chainClosureStep ttWord ttFiber30Prefix57 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 38 ∈
      chainClosureStep ttWord ttFiber30Prefix56 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix56 = ttFiber30Prefix38 ++ [ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56]
      (chainClosureStep ttWord ttFiber30Prefix38 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 38) ttFiber30State38_in_pass1_prefix38
  rw [show ttFiber30Prefix57 = ttFiber30Prefix56 ++ [ttFiber30StateAt 57] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 57) []
    (chainClosureStep ttWord ttFiber30Prefix56 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 38) hparentBefore ttFiber30ReverseSingleStep57

theorem ttFiber30State57_in_pass1_full :
    ttFiber30StateAt 57 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix57 ++ [ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix57 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 57) ttFiber30State57_in_pass1_prefix57

theorem ttFiber30State58_in_pass1_prefix58 :
    ttFiber30StateAt 58 ∈ chainClosureStep ttWord ttFiber30Prefix58 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 36 ∈
      chainClosureStep ttWord ttFiber30Prefix57 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix57 = ttFiber30Prefix36 ++ [ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57]
      (chainClosureStep ttWord ttFiber30Prefix36 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 36) ttFiber30State36_in_pass1_prefix36
  rw [show ttFiber30Prefix58 = ttFiber30Prefix57 ++ [ttFiber30StateAt 58] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 58) []
    (chainClosureStep ttWord ttFiber30Prefix57 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 36) hparentBefore ttFiber30ReverseSingleStep58

theorem ttFiber30State58_in_pass1_full :
    ttFiber30StateAt 58 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix58 ++ [ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix58 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 58) ttFiber30State58_in_pass1_prefix58

theorem ttFiber30State59_in_pass1_prefix59 :
    ttFiber30StateAt 59 ∈ chainClosureStep ttWord ttFiber30Prefix59 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 37 ∈
      chainClosureStep ttWord ttFiber30Prefix58 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix58 = ttFiber30Prefix37 ++ [ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58]
      (chainClosureStep ttWord ttFiber30Prefix37 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 37) ttFiber30State37_in_pass1_prefix37
  rw [show ttFiber30Prefix59 = ttFiber30Prefix58 ++ [ttFiber30StateAt 59] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 59) []
    (chainClosureStep ttWord ttFiber30Prefix58 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 37) hparentBefore ttFiber30ReverseSingleStep59

theorem ttFiber30State59_in_pass1_full :
    ttFiber30StateAt 59 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix59 ++ [ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix59 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 59) ttFiber30State59_in_pass1_prefix59

theorem ttFiber30State60_in_pass1_prefix60 :
    ttFiber30StateAt 60 ∈ chainClosureStep ttWord ttFiber30Prefix60 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 32 ∈
      chainClosureStep ttWord ttFiber30Prefix59 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix59 = ttFiber30Prefix32 ++ [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59]
      (chainClosureStep ttWord ttFiber30Prefix32 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 32) ttFiber30State32_in_pass1_prefix32
  rw [show ttFiber30Prefix60 = ttFiber30Prefix59 ++ [ttFiber30StateAt 60] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 60) []
    (chainClosureStep ttWord ttFiber30Prefix59 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 32) hparentBefore ttFiber30ReverseSingleStep60

theorem ttFiber30State60_in_pass1_full :
    ttFiber30StateAt 60 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix60 ++ [ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix60 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 60) ttFiber30State60_in_pass1_prefix60

theorem ttFiber30State61_in_pass1_prefix61 :
    ttFiber30StateAt 61 ∈ chainClosureStep ttWord ttFiber30Prefix61 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 33 ∈
      chainClosureStep ttWord ttFiber30Prefix60 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix60 = ttFiber30Prefix33 ++ [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60]
      (chainClosureStep ttWord ttFiber30Prefix33 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 33) ttFiber30State33_in_pass1_prefix33
  rw [show ttFiber30Prefix61 = ttFiber30Prefix60 ++ [ttFiber30StateAt 61] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 61) []
    (chainClosureStep ttWord ttFiber30Prefix60 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 33) hparentBefore ttFiber30ReverseSingleStep61

theorem ttFiber30State61_in_pass1_full :
    ttFiber30StateAt 61 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix61 ++ [ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix61 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 61) ttFiber30State61_in_pass1_prefix61

theorem ttFiber30State62_in_pass1_prefix62 :
    ttFiber30StateAt 62 ∈ chainClosureStep ttWord ttFiber30Prefix62 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 34 ∈
      chainClosureStep ttWord ttFiber30Prefix61 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix61 = ttFiber30Prefix34 ++ [ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61]
      (chainClosureStep ttWord ttFiber30Prefix34 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 34) ttFiber30State34_in_pass1_prefix34
  rw [show ttFiber30Prefix62 = ttFiber30Prefix61 ++ [ttFiber30StateAt 62] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 62) []
    (chainClosureStep ttWord ttFiber30Prefix61 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 34) hparentBefore ttFiber30ReverseSingleStep62

theorem ttFiber30State62_in_pass1_full :
    ttFiber30StateAt 62 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix62 ++ [ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix62 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 62) ttFiber30State62_in_pass1_prefix62

theorem ttFiber30State63_in_pass1_prefix63 :
    ttFiber30StateAt 63 ∈ chainClosureStep ttWord ttFiber30Prefix63 ([ttFiber30StateAt 0]) := by
  have hparentBefore : ttFiber30StateAt 35 ∈
      chainClosureStep ttWord ttFiber30Prefix62 ([ttFiber30StateAt 0]) := by
    rw [show ttFiber30Prefix62 = ttFiber30Prefix35 ++ [ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62]
      (chainClosureStep ttWord ttFiber30Prefix35 ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 35) ttFiber30State35_in_pass1_prefix35
  rw [show ttFiber30Prefix63 = ttFiber30Prefix62 ++ [ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 63) []
    (chainClosureStep ttWord ttFiber30Prefix62 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 35) hparentBefore ttFiber30ReverseSingleStep63

theorem ttFiber30State63_in_pass1_full :
    ttFiber30StateAt 63 ∈ chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix63 ++ [] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord []
    (chainClosureStep ttWord ttFiber30Prefix63 ([ttFiber30StateAt 0]))
    (ttFiber30StateAt 63) ttFiber30State63_in_pass1_prefix63

theorem ttFiber30State5_in_pass2_prefix5 :
    ttFiber30StateAt 5 ∈ chainClosureStep ttWord ttFiber30Prefix5 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
  have hparentBefore : ttFiber30StateAt 7 ∈
      chainClosureStep ttWord ttFiber30Prefix4 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
    exact chainClosureStep_mem_of_seen ttWord ttFiber30Prefix4
      (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0]))
      (ttFiber30StateAt 7) ttFiber30State7_in_pass1_full
  rw [show ttFiber30Prefix5 = ttFiber30Prefix4 ++ [ttFiber30StateAt 5] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 5) []
    (chainClosureStep ttWord ttFiber30Prefix4 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])))
    (ttFiber30StateAt 7) hparentBefore ttFiber30ReverseSingleStep5

theorem ttFiber30State5_in_pass2_full :
    ttFiber30StateAt 5 ∈ chainClosureStep ttWord ttFiber30DirectStates (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix5 ++ [ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12, ttFiber30StateAt 13, ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix5 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])))
    (ttFiber30StateAt 5) ttFiber30State5_in_pass2_prefix5

theorem ttFiber30State13_in_pass2_prefix13 :
    ttFiber30StateAt 13 ∈ chainClosureStep ttWord ttFiber30Prefix13 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
  have hparentBefore : ttFiber30StateAt 5 ∈
      chainClosureStep ttWord ttFiber30Prefix12 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
    rw [show ttFiber30Prefix12 = ttFiber30Prefix5 ++ [ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12] by decide]
    rw [chainClosureStep_append]
    exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 6, ttFiber30StateAt 7, ttFiber30StateAt 8, ttFiber30StateAt 9, ttFiber30StateAt 10, ttFiber30StateAt 11, ttFiber30StateAt 12]
      (chainClosureStep ttWord ttFiber30Prefix5 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])))
      (ttFiber30StateAt 5) ttFiber30State5_in_pass2_prefix5
  rw [show ttFiber30Prefix13 = ttFiber30Prefix12 ++ [ttFiber30StateAt 13] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_cons_mem_of_seen_step ttWord (ttFiber30StateAt 13) []
    (chainClosureStep ttWord ttFiber30Prefix12 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])))
    (ttFiber30StateAt 5) hparentBefore ttFiber30ReverseSingleStep13

theorem ttFiber30State13_in_pass2_full :
    ttFiber30StateAt 13 ∈ chainClosureStep ttWord ttFiber30DirectStates (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])) := by
  rw [show ttFiber30DirectStates = ttFiber30Prefix13 ++ [ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63] by decide]
  rw [chainClosureStep_append]
  exact chainClosureStep_mem_of_seen ttWord [ttFiber30StateAt 14, ttFiber30StateAt 15, ttFiber30StateAt 16, ttFiber30StateAt 17, ttFiber30StateAt 18, ttFiber30StateAt 19, ttFiber30StateAt 20, ttFiber30StateAt 21, ttFiber30StateAt 22, ttFiber30StateAt 23, ttFiber30StateAt 24, ttFiber30StateAt 25, ttFiber30StateAt 26, ttFiber30StateAt 27, ttFiber30StateAt 28, ttFiber30StateAt 29, ttFiber30StateAt 30, ttFiber30StateAt 31, ttFiber30StateAt 32, ttFiber30StateAt 33, ttFiber30StateAt 34, ttFiber30StateAt 35, ttFiber30StateAt 36, ttFiber30StateAt 37, ttFiber30StateAt 38, ttFiber30StateAt 39, ttFiber30StateAt 40, ttFiber30StateAt 41, ttFiber30StateAt 42, ttFiber30StateAt 43, ttFiber30StateAt 44, ttFiber30StateAt 45, ttFiber30StateAt 46, ttFiber30StateAt 47, ttFiber30StateAt 48, ttFiber30StateAt 49, ttFiber30StateAt 50, ttFiber30StateAt 51, ttFiber30StateAt 52, ttFiber30StateAt 53, ttFiber30StateAt 54, ttFiber30StateAt 55, ttFiber30StateAt 56, ttFiber30StateAt 57, ttFiber30StateAt 58, ttFiber30StateAt 59, ttFiber30StateAt 60, ttFiber30StateAt 61, ttFiber30StateAt 62, ttFiber30StateAt 63]
    (chainClosureStep ttWord ttFiber30Prefix13 (chainClosureStep ttWord ttFiber30DirectStates ([ttFiber30StateAt 0])))
    (ttFiber30StateAt 13) ttFiber30State13_in_pass2_prefix13

theorem ttFiber30State0_in_close :
    ttFiber30StateAt 0 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  exact closeChainFiber_mem_of_seen ttWord ttFiber30DirectStates ttFiber30DirectStates.length
    [ttFiber30StateAt 0] (ttFiber30StateAt 0) (by simp)

theorem ttFiber30State1_in_close :
    ttFiber30StateAt 1 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 1 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 1) ttFiber30State1_in_pass1_full

theorem ttFiber30State2_in_close :
    ttFiber30StateAt 2 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 2 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 2) ttFiber30State2_in_pass1_full

theorem ttFiber30State3_in_close :
    ttFiber30StateAt 3 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 3 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 3) ttFiber30State3_in_pass1_full

theorem ttFiber30State4_in_close :
    ttFiber30StateAt 4 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 4 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 4) ttFiber30State4_in_pass1_full

theorem ttFiber30State5_in_close :
    ttFiber30StateAt 5 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 5 ∈ closeChainFiber ttWord ttFiber30DirectStates (62 + 2)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber30DirectStates 62
    [ttFiber30StateAt 0] (ttFiber30StateAt 5) ttFiber30FirstPassGrows
    ttFiber30State5_in_pass2_full

theorem ttFiber30State6_in_close :
    ttFiber30StateAt 6 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 6 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 6) ttFiber30State6_in_pass1_full

theorem ttFiber30State7_in_close :
    ttFiber30StateAt 7 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 7 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 7) ttFiber30State7_in_pass1_full

theorem ttFiber30State8_in_close :
    ttFiber30StateAt 8 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 8 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 8) ttFiber30State8_in_pass1_full

theorem ttFiber30State9_in_close :
    ttFiber30StateAt 9 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 9 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 9) ttFiber30State9_in_pass1_full

theorem ttFiber30State10_in_close :
    ttFiber30StateAt 10 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 10 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 10) ttFiber30State10_in_pass1_full

theorem ttFiber30State11_in_close :
    ttFiber30StateAt 11 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 11 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 11) ttFiber30State11_in_pass1_full

theorem ttFiber30State12_in_close :
    ttFiber30StateAt 12 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 12 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 12) ttFiber30State12_in_pass1_full

theorem ttFiber30State13_in_close :
    ttFiber30StateAt 13 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 13 ∈ closeChainFiber ttWord ttFiber30DirectStates (62 + 2)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_second_closureStep ttWord ttFiber30DirectStates 62
    [ttFiber30StateAt 0] (ttFiber30StateAt 13) ttFiber30FirstPassGrows
    ttFiber30State13_in_pass2_full

theorem ttFiber30State14_in_close :
    ttFiber30StateAt 14 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 14 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 14) ttFiber30State14_in_pass1_full

theorem ttFiber30State15_in_close :
    ttFiber30StateAt 15 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 15 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 15) ttFiber30State15_in_pass1_full

theorem ttFiber30State16_in_close :
    ttFiber30StateAt 16 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 16 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 16) ttFiber30State16_in_pass1_full

theorem ttFiber30State17_in_close :
    ttFiber30StateAt 17 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 17 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 17) ttFiber30State17_in_pass1_full

theorem ttFiber30State18_in_close :
    ttFiber30StateAt 18 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 18 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 18) ttFiber30State18_in_pass1_full

theorem ttFiber30State19_in_close :
    ttFiber30StateAt 19 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 19 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 19) ttFiber30State19_in_pass1_full

theorem ttFiber30State20_in_close :
    ttFiber30StateAt 20 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 20 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 20) ttFiber30State20_in_pass1_full

theorem ttFiber30State21_in_close :
    ttFiber30StateAt 21 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 21 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 21) ttFiber30State21_in_pass1_full

theorem ttFiber30State22_in_close :
    ttFiber30StateAt 22 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 22 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 22) ttFiber30State22_in_pass1_full

theorem ttFiber30State23_in_close :
    ttFiber30StateAt 23 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 23 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 23) ttFiber30State23_in_pass1_full

theorem ttFiber30State24_in_close :
    ttFiber30StateAt 24 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 24 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 24) ttFiber30State24_in_pass1_full

theorem ttFiber30State25_in_close :
    ttFiber30StateAt 25 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 25 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 25) ttFiber30State25_in_pass1_full

theorem ttFiber30State26_in_close :
    ttFiber30StateAt 26 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 26 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 26) ttFiber30State26_in_pass1_full

theorem ttFiber30State27_in_close :
    ttFiber30StateAt 27 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 27 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 27) ttFiber30State27_in_pass1_full

theorem ttFiber30State28_in_close :
    ttFiber30StateAt 28 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 28 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 28) ttFiber30State28_in_pass1_full

theorem ttFiber30State29_in_close :
    ttFiber30StateAt 29 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 29 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 29) ttFiber30State29_in_pass1_full

theorem ttFiber30State30_in_close :
    ttFiber30StateAt 30 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 30 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 30) ttFiber30State30_in_pass1_full

theorem ttFiber30State31_in_close :
    ttFiber30StateAt 31 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 31 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 31) ttFiber30State31_in_pass1_full

theorem ttFiber30State32_in_close :
    ttFiber30StateAt 32 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 32 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 32) ttFiber30State32_in_pass1_full

theorem ttFiber30State33_in_close :
    ttFiber30StateAt 33 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 33 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 33) ttFiber30State33_in_pass1_full

theorem ttFiber30State34_in_close :
    ttFiber30StateAt 34 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 34 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 34) ttFiber30State34_in_pass1_full

theorem ttFiber30State35_in_close :
    ttFiber30StateAt 35 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 35 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 35) ttFiber30State35_in_pass1_full

theorem ttFiber30State36_in_close :
    ttFiber30StateAt 36 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 36 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 36) ttFiber30State36_in_pass1_full

theorem ttFiber30State37_in_close :
    ttFiber30StateAt 37 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 37 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 37) ttFiber30State37_in_pass1_full

theorem ttFiber30State38_in_close :
    ttFiber30StateAt 38 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 38 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 38) ttFiber30State38_in_pass1_full

theorem ttFiber30State39_in_close :
    ttFiber30StateAt 39 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 39 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 39) ttFiber30State39_in_pass1_full

theorem ttFiber30State40_in_close :
    ttFiber30StateAt 40 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 40 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 40) ttFiber30State40_in_pass1_full

theorem ttFiber30State41_in_close :
    ttFiber30StateAt 41 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 41 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 41) ttFiber30State41_in_pass1_full

theorem ttFiber30State42_in_close :
    ttFiber30StateAt 42 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 42 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 42) ttFiber30State42_in_pass1_full

theorem ttFiber30State43_in_close :
    ttFiber30StateAt 43 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 43 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 43) ttFiber30State43_in_pass1_full

theorem ttFiber30State44_in_close :
    ttFiber30StateAt 44 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 44 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 44) ttFiber30State44_in_pass1_full

theorem ttFiber30State45_in_close :
    ttFiber30StateAt 45 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 45 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 45) ttFiber30State45_in_pass1_full

theorem ttFiber30State46_in_close :
    ttFiber30StateAt 46 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 46 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 46) ttFiber30State46_in_pass1_full

theorem ttFiber30State47_in_close :
    ttFiber30StateAt 47 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 47 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 47) ttFiber30State47_in_pass1_full

theorem ttFiber30State48_in_close :
    ttFiber30StateAt 48 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 48 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 48) ttFiber30State48_in_pass1_full

theorem ttFiber30State49_in_close :
    ttFiber30StateAt 49 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 49 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 49) ttFiber30State49_in_pass1_full

theorem ttFiber30State50_in_close :
    ttFiber30StateAt 50 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 50 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 50) ttFiber30State50_in_pass1_full

theorem ttFiber30State51_in_close :
    ttFiber30StateAt 51 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 51 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 51) ttFiber30State51_in_pass1_full

theorem ttFiber30State52_in_close :
    ttFiber30StateAt 52 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 52 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 52) ttFiber30State52_in_pass1_full

theorem ttFiber30State53_in_close :
    ttFiber30StateAt 53 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 53 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 53) ttFiber30State53_in_pass1_full

theorem ttFiber30State54_in_close :
    ttFiber30StateAt 54 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 54 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 54) ttFiber30State54_in_pass1_full

theorem ttFiber30State55_in_close :
    ttFiber30StateAt 55 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 55 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 55) ttFiber30State55_in_pass1_full

theorem ttFiber30State56_in_close :
    ttFiber30StateAt 56 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 56 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 56) ttFiber30State56_in_pass1_full

theorem ttFiber30State57_in_close :
    ttFiber30StateAt 57 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 57 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 57) ttFiber30State57_in_pass1_full

theorem ttFiber30State58_in_close :
    ttFiber30StateAt 58 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 58 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 58) ttFiber30State58_in_pass1_full

theorem ttFiber30State59_in_close :
    ttFiber30StateAt 59 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 59 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 59) ttFiber30State59_in_pass1_full

theorem ttFiber30State60_in_close :
    ttFiber30StateAt 60 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 60 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 60) ttFiber30State60_in_pass1_full

theorem ttFiber30State61_in_close :
    ttFiber30StateAt 61 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 61 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 61) ttFiber30State61_in_pass1_full

theorem ttFiber30State62_in_close :
    ttFiber30StateAt 62 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 62 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 62) ttFiber30State62_in_pass1_full

theorem ttFiber30State63_in_close :
    ttFiber30StateAt 63 ∈
      closeChainFiber ttWord ttFiber30DirectStates ttFiber30DirectStates.length
        [ttFiber30StateAt 0] := by
  change ttFiber30StateAt 63 ∈ closeChainFiber ttWord ttFiber30DirectStates (63 + 1)
    [ttFiber30StateAt 0]
  exact closeChainFiber_mem_of_closureStep ttWord ttFiber30DirectStates 63
    [ttFiber30StateAt 0] (ttFiber30StateAt 63) ttFiber30State63_in_pass1_full

theorem ttFiber30DirectConnected :
    chainFiberConnected ttWord ttFiber30DirectStates = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  simp only [ttFiber30DirectStates, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · subst state
    exact ttFiber30State0_in_close
  · subst state
    exact ttFiber30State1_in_close
  · subst state
    exact ttFiber30State2_in_close
  · subst state
    exact ttFiber30State3_in_close
  · subst state
    exact ttFiber30State4_in_close
  · subst state
    exact ttFiber30State5_in_close
  · subst state
    exact ttFiber30State6_in_close
  · subst state
    exact ttFiber30State7_in_close
  · subst state
    exact ttFiber30State8_in_close
  · subst state
    exact ttFiber30State9_in_close
  · subst state
    exact ttFiber30State10_in_close
  · subst state
    exact ttFiber30State11_in_close
  · subst state
    exact ttFiber30State12_in_close
  · subst state
    exact ttFiber30State13_in_close
  · subst state
    exact ttFiber30State14_in_close
  · subst state
    exact ttFiber30State15_in_close
  · subst state
    exact ttFiber30State16_in_close
  · subst state
    exact ttFiber30State17_in_close
  · subst state
    exact ttFiber30State18_in_close
  · subst state
    exact ttFiber30State19_in_close
  · subst state
    exact ttFiber30State20_in_close
  · subst state
    exact ttFiber30State21_in_close
  · subst state
    exact ttFiber30State22_in_close
  · subst state
    exact ttFiber30State23_in_close
  · subst state
    exact ttFiber30State24_in_close
  · subst state
    exact ttFiber30State25_in_close
  · subst state
    exact ttFiber30State26_in_close
  · subst state
    exact ttFiber30State27_in_close
  · subst state
    exact ttFiber30State28_in_close
  · subst state
    exact ttFiber30State29_in_close
  · subst state
    exact ttFiber30State30_in_close
  · subst state
    exact ttFiber30State31_in_close
  · subst state
    exact ttFiber30State32_in_close
  · subst state
    exact ttFiber30State33_in_close
  · subst state
    exact ttFiber30State34_in_close
  · subst state
    exact ttFiber30State35_in_close
  · subst state
    exact ttFiber30State36_in_close
  · subst state
    exact ttFiber30State37_in_close
  · subst state
    exact ttFiber30State38_in_close
  · subst state
    exact ttFiber30State39_in_close
  · subst state
    exact ttFiber30State40_in_close
  · subst state
    exact ttFiber30State41_in_close
  · subst state
    exact ttFiber30State42_in_close
  · subst state
    exact ttFiber30State43_in_close
  · subst state
    exact ttFiber30State44_in_close
  · subst state
    exact ttFiber30State45_in_close
  · subst state
    exact ttFiber30State46_in_close
  · subst state
    exact ttFiber30State47_in_close
  · subst state
    exact ttFiber30State48_in_close
  · subst state
    exact ttFiber30State49_in_close
  · subst state
    exact ttFiber30State50_in_close
  · subst state
    exact ttFiber30State51_in_close
  · subst state
    exact ttFiber30State52_in_close
  · subst state
    exact ttFiber30State53_in_close
  · subst state
    exact ttFiber30State54_in_close
  · subst state
    exact ttFiber30State55_in_close
  · subst state
    exact ttFiber30State56_in_close
  · subst state
    exact ttFiber30State57_in_close
  · subst state
    exact ttFiber30State58_in_close
  · subst state
    exact ttFiber30State59_in_close
  · subst state
    exact ttFiber30State60_in_close
  · subst state
    exact ttFiber30State61_in_close
  · subst state
    exact ttFiber30State62_in_close
  · subst state
    exact ttFiber30State63_in_close
  · cases h

end GoertzelLemma818LengthTwoDirectClosureMultiPassPrototype

end Mettapedia.GraphTheory.FourColor
