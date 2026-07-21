import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfiguration

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateFastHypermapCheck

open ClassicalCertificateConfiguration

/-- Compact executable permutation check: every entry is in range and differs
from all earlier entries. -/
def tableBoolean (size : Nat) (table : Array Nat) : Bool :=
  decide (table.size = size) &&
    (List.range size).all fun index =>
      decide (HypermapCode.lookup table index < size) &&
        (List.range index).all fun earlier =>
          decide
            (HypermapCode.lookup table earlier ≠
              HypermapCode.lookup table index)

theorem tableBoolean_size {size : Nat} {table : Array Nat}
    (hcheck : tableBoolean size table = true) :
    table.size = size := by
  have hparts :
      decide (table.size = size) = true ∧
        (List.range size).all (fun index =>
          decide (HypermapCode.lookup table index < size) &&
            (List.range index).all fun earlier =>
              decide
                (HypermapCode.lookup table earlier ≠
                  HypermapCode.lookup table index)) = true := by
    simpa [tableBoolean] using hcheck
  exact of_decide_eq_true hparts.1

theorem tableBoolean_bound {size : Nat} {table : Array Nat}
    (hcheck : tableBoolean size table = true)
    (index : Nat) (hindex : index < size) :
    HypermapCode.lookup table index < size := by
  have hparts :
      decide (table.size = size) = true ∧
        (List.range size).all (fun index =>
          decide (HypermapCode.lookup table index < size) &&
            (List.range index).all fun earlier =>
              decide
                (HypermapCode.lookup table earlier ≠
                  HypermapCode.lookup table index)) = true := by
    simpa [tableBoolean] using hcheck
  have hrow := (List.all_eq_true.1 hparts.2)
    index (List.mem_range.2 hindex)
  have hrowParts :
      decide (HypermapCode.lookup table index < size) = true ∧
        (List.range index).all (fun earlier =>
          decide
            (HypermapCode.lookup table earlier ≠
              HypermapCode.lookup table index)) = true := by
    simpa using hrow
  exact of_decide_eq_true hrowParts.1

theorem tableBoolean_ne_of_lt {size : Nat} {table : Array Nat}
    (hcheck : tableBoolean size table = true)
    {earlier index : Nat} (hearlier : earlier < index)
    (hindex : index < size) :
    HypermapCode.lookup table earlier ≠
      HypermapCode.lookup table index := by
  have hparts :
      decide (table.size = size) = true ∧
        (List.range size).all (fun index =>
          decide (HypermapCode.lookup table index < size) &&
            (List.range index).all fun earlier =>
              decide
                (HypermapCode.lookup table earlier ≠
                  HypermapCode.lookup table index)) = true := by
    simpa [tableBoolean] using hcheck
  have hrow := (List.all_eq_true.1 hparts.2)
    index (List.mem_range.2 hindex)
  have hrowParts :
      decide (HypermapCode.lookup table index < size) = true ∧
        (List.range index).all (fun earlier =>
          decide
            (HypermapCode.lookup table earlier ≠
              HypermapCode.lookup table index)) = true := by
    simpa using hrow
  have hne := (List.all_eq_true.1 hrowParts.2)
    earlier (List.mem_range.2 hearlier)
  exact of_decide_eq_true hne

theorem tableBoolean_isPermutation {size : Nat} {table : Array Nat}
    (hcheck : tableBoolean size table = true) :
    RawTable.IsPermutation
      (fun dart : Fin size => HypermapCode.lookup table dart.val) := by
  constructor
  · intro dart
    exact tableBoolean_bound hcheck dart.val dart.isLt
  · intro left right heq
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact (tableBoolean_ne_of_lt hcheck hlt right.isLt) heq
    · exact (tableBoolean_ne_of_lt hcheck hgt left.isLt) heq.symm

def triangleBoolean (code : HypermapCode) : Bool :=
  (List.range code.dartCount).all fun dart =>
    decide
      (HypermapCode.lookup code.node
          (HypermapCode.lookup code.face
            (HypermapCode.lookup code.edge dart)) = dart)

def checker (code : HypermapCode) : Bool :=
  tableBoolean code.dartCount code.edge &&
    (tableBoolean code.dartCount code.node &&
      (tableBoolean code.dartCount code.face && triangleBoolean code))

/-- The compact Boolean checker implies the standard semantic certificate
predicate. -/
theorem accepted_of_checker_true (code : HypermapCode)
    (hcheck : checker code = true) : code.Accepted := by
  have hparts :
      tableBoolean code.dartCount code.edge = true ∧
        tableBoolean code.dartCount code.node = true ∧
          tableBoolean code.dartCount code.face = true ∧
            triangleBoolean code = true := by
    simpa [checker] using hcheck
  have hedge := tableBoolean_isPermutation hparts.1
  have hnode := tableBoolean_isPermutation hparts.2.1
  have hface := tableBoolean_isPermutation hparts.2.2.1
  refine ⟨tableBoolean_size hparts.1,
    tableBoolean_size hparts.2.1,
    tableBoolean_size hparts.2.2.1, hedge, hnode, hface, ?_⟩
  intro dart
  have hedgeBound := tableBoolean_bound hparts.1 dart.val dart.isLt
  have hfaceBound := tableBoolean_bound hparts.2.2.1
    (HypermapCode.lookup code.edge dart.val) hedgeBound
  have hnodeBound := tableBoolean_bound hparts.2.1
    (HypermapCode.lookup code.face
      (HypermapCode.lookup code.edge dart.val)) hfaceBound
  have htriangle := (List.all_eq_true.1 hparts.2.2.2)
    dart.val (List.mem_range.2 dart.isLt)
  apply Fin.ext
  simpa [HypermapCode.decode, RawTable.toFin, hedgeBound, hfaceBound,
    hnodeBound] using (of_decide_eq_true htriangle)

/-- A materialized hypermap together with explicit inverse tables for its
three permutations. -/
structure InverseCode where
  hypermap : HypermapCode
  edgeInverse : Array Nat
  nodeInverse : Array Nat
  faceInverse : Array Nat
  deriving DecidableEq

namespace InverseCode

def inverseTableBoolean (size : Nat) (table inverse : Array Nat) : Bool :=
  decide (table.size = size) &&
    (decide (inverse.size = size) &&
      (List.range size).all fun index =>
        decide (HypermapCode.lookup table index < size) &&
          decide
            (HypermapCode.lookup inverse
              (HypermapCode.lookup table index) = index))

theorem inverseTableBoolean_parts {size : Nat} {table inverse : Array Nat}
    (hcheck : inverseTableBoolean size table inverse = true) :
    decide (table.size = size) = true ∧
      decide (inverse.size = size) = true ∧
        (List.range size).all (fun index =>
          decide (HypermapCode.lookup table index < size) &&
            decide
              (HypermapCode.lookup inverse
                (HypermapCode.lookup table index) = index)) = true := by
  simpa [inverseTableBoolean] using hcheck

theorem inverseTableBoolean_size {size : Nat} {table inverse : Array Nat}
    (hcheck : inverseTableBoolean size table inverse = true) :
    table.size = size := by
  exact of_decide_eq_true (inverseTableBoolean_parts hcheck).1

theorem inverseTableBoolean_bound {size : Nat} {table inverse : Array Nat}
    (hcheck : inverseTableBoolean size table inverse = true)
    (index : Nat) (hindex : index < size) :
    HypermapCode.lookup table index < size := by
  have hrow :=
    (List.all_eq_true.1 (inverseTableBoolean_parts hcheck).2.2)
      index (List.mem_range.2 hindex)
  have hrowParts :
      decide (HypermapCode.lookup table index < size) = true ∧
        decide
          (HypermapCode.lookup inverse
            (HypermapCode.lookup table index) = index) = true := by
    simpa using hrow
  exact of_decide_eq_true hrowParts.1

theorem inverseTableBoolean_leftInverse
    {size : Nat} {table inverse : Array Nat}
    (hcheck : inverseTableBoolean size table inverse = true)
    (index : Nat) (hindex : index < size) :
    HypermapCode.lookup inverse (HypermapCode.lookup table index) = index := by
  have hrow :=
    (List.all_eq_true.1 (inverseTableBoolean_parts hcheck).2.2)
      index (List.mem_range.2 hindex)
  have hrowParts :
      decide (HypermapCode.lookup table index < size) = true ∧
        decide
          (HypermapCode.lookup inverse
            (HypermapCode.lookup table index) = index) = true := by
    simpa using hrow
  exact of_decide_eq_true hrowParts.2

theorem inverseTableBoolean_isPermutation
    {size : Nat} {table inverse : Array Nat}
    (hcheck : inverseTableBoolean size table inverse = true) :
    RawTable.IsPermutation
      (fun dart : Fin size => HypermapCode.lookup table dart.val) := by
  constructor
  · intro dart
    exact inverseTableBoolean_bound hcheck dart.val dart.isLt
  · intro left right heq
    apply Fin.ext
    calc
      left.val = HypermapCode.lookup inverse
          (HypermapCode.lookup table left.val) :=
        (inverseTableBoolean_leftInverse hcheck left.val left.isLt).symm
      _ = HypermapCode.lookup inverse
          (HypermapCode.lookup table right.val) :=
        congrArg (HypermapCode.lookup inverse) heq
      _ = right.val :=
        inverseTableBoolean_leftInverse hcheck right.val right.isLt

def checker (code : InverseCode) : Bool :=
  inverseTableBoolean code.hypermap.dartCount code.hypermap.edge
      code.edgeInverse &&
    (inverseTableBoolean code.hypermap.dartCount code.hypermap.node
        code.nodeInverse &&
      (inverseTableBoolean code.hypermap.dartCount code.hypermap.face
          code.faceInverse && triangleBoolean code.hypermap))

/-- A successful inverse-table check produces the standard accepted hypermap
certificate. -/
theorem accepted_of_checker_true (code : InverseCode)
    (hcheck : code.checker = true) : code.hypermap.Accepted := by
  have hparts :
      inverseTableBoolean code.hypermap.dartCount code.hypermap.edge
          code.edgeInverse = true ∧
        inverseTableBoolean code.hypermap.dartCount code.hypermap.node
            code.nodeInverse = true ∧
          inverseTableBoolean code.hypermap.dartCount code.hypermap.face
              code.faceInverse = true ∧
            triangleBoolean code.hypermap = true := by
    simpa [checker] using hcheck
  have hedge := inverseTableBoolean_isPermutation hparts.1
  have hnode := inverseTableBoolean_isPermutation hparts.2.1
  have hface := inverseTableBoolean_isPermutation hparts.2.2.1
  refine ⟨inverseTableBoolean_size hparts.1,
    inverseTableBoolean_size hparts.2.1,
    inverseTableBoolean_size hparts.2.2.1, hedge, hnode, hface, ?_⟩
  intro dart
  have hedgeBound :=
    inverseTableBoolean_bound hparts.1 dart.val dart.isLt
  have hfaceBound := inverseTableBoolean_bound hparts.2.2.1
    (HypermapCode.lookup code.hypermap.edge dart.val) hedgeBound
  have hnodeBound := inverseTableBoolean_bound hparts.2.1
    (HypermapCode.lookup code.hypermap.face
      (HypermapCode.lookup code.hypermap.edge dart.val)) hfaceBound
  have htriangle := (List.all_eq_true.1 hparts.2.2.2)
    dart.val (List.mem_range.2 dart.isLt)
  apply Fin.ext
  simpa [HypermapCode.decode, RawTable.toFin, hedgeBound, hfaceBound,
    hnodeBound] using (of_decide_eq_true htriangle)

end InverseCode

end ClassicalCertificateFastHypermapCheck

end Mettapedia.GraphTheory.FourColor
