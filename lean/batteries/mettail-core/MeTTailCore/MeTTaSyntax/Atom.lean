/-!
# Shared MeTTa atom structure

Finite atom syntax and payload snapshots shared by independent HE mathematics
and implementation clients. The `Metta` namespace names the shared structure;
it does not designate an interpreter or an HE semantic specification.

This dependency leaf defines the carriers, their constructor-directed Boolean
comparisons, structural size and variable occurrences. It has no imports.
Matching, numeric equivalence, type designators, evaluation outcomes and
control policies are specified by its clients. The constructors are retained
from the existing atom carrier so all clients use one type, without aliases
or a second implementation-specific copy.
-/

namespace Metta

/-- Names of MeTTa variables, without the leading `$`. -/
abbrev VarName := String

/- Structural snapshots may contain further binding snapshots. These finite
carriers describe serialized payloads, not live binding tables or their
operational meaning. -/
mutual
  inductive StoredGround where
    | int : Int → StoredGround
    | float : Float → StoredGround
    | str : String → StoredGround
    | bool : Bool → StoredGround
    | unit : StoredGround
    | error : String → StoredGround
    | external : String → String → StoredGround
    | bindings : List StoredBinding → StoredGround
    deriving Repr, Inhabited

  inductive StoredAtom where
    | sym : String → StoredAtom
    | var : VarName → StoredAtom
    | gnd : StoredGround → StoredAtom
    | expr : List StoredAtom → StoredAtom
    deriving Repr, Inhabited

  inductive StoredBinding where
    | val : VarName → StoredAtom → StoredBinding
    | eq : VarName → VarName → StoredBinding
    deriving Repr, Inhabited
end

mutual

/-- Reducible structural equality for grounded values stored by
`collapse-bind`. -/
def StoredGround.beq : StoredGround → StoredGround → Bool
  | .int left, .int right => left == right
  | .float left, .float right => left == right
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .unit, .unit => true
  | .error left, .error right => left == right
  | .external leftTag leftPayload, .external rightTag rightPayload =>
      leftTag == rightTag && leftPayload == rightPayload
  | .bindings left, .bindings right => StoredBinding.beqList left right
  | _, _ => false

/-- Reducible structural equality for atoms stored by `collapse-bind`. -/
def StoredAtom.beq : StoredAtom → StoredAtom → Bool
  | .sym left, .sym right => left == right
  | .var left, .var right => left == right
  | .gnd left, .gnd right => StoredGround.beq left right
  | .expr left, .expr right => StoredAtom.beqList left right
  | _, _ => false

/-- Pointwise structural equality for stored atom lists. -/
def StoredAtom.beqList : List StoredAtom → List StoredAtom → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      StoredAtom.beq left right && StoredAtom.beqList lefts rights
  | _, _ => false

/-- Reducible structural equality for one stored binding relation. -/
def StoredBinding.beq : StoredBinding → StoredBinding → Bool
  | .val leftName leftValue, .val rightName rightValue =>
      leftName == rightName && StoredAtom.beq leftValue rightValue
  | .eq leftA leftB, .eq rightA rightB =>
      leftA == rightA && leftB == rightB
  | _, _ => false

/-- Pointwise structural equality for stored binding lists. -/
def StoredBinding.beqList : List StoredBinding → List StoredBinding → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      StoredBinding.beq left right && StoredBinding.beqList lefts rights
  | _, _ => false

end


instance : BEq StoredGround := ⟨StoredGround.beq⟩
instance : BEq StoredAtom := ⟨StoredAtom.beq⟩
instance : BEq StoredBinding := ⟨StoredBinding.beq⟩

/-- Structural payload forms. `external` carries an uninterpreted tag and text;
`bindings` carries a finite snapshot. A language or runtime must separately
specify how any of these forms is interpreted. -/
inductive Ground where
  | int : Int → Ground
  | float : Float → Ground
  | str : String → Ground
  | bool : Bool → Ground
  | unit : Ground
  | error : String → Ground
  | external : String → String → Ground
  | bindings : List StoredBinding → Ground
  deriving Repr, BEq, Inhabited

/-- Reducible structural equality for live grounded payloads. -/
def Ground.beq : Ground → Ground → Bool
  | .int left, .int right => left == right
  | .float left, .float right => left == right
  | .str left, .str right => left == right
  | .bool left, .bool right => left == right
  | .unit, .unit => true
  | .error left, .error right => left == right
  | .external leftTag leftPayload, .external rightTag rightPayload =>
      leftTag == rightTag && leftPayload == rightPayload
  | .bindings left, .bindings right => StoredBinding.beqList left right
  | _, _ => false

/-- MeTTa atoms: symbols, variables, grounded atoms, and expressions. -/
inductive Atom where
  | sym : String → Atom
  | var : VarName → Atom
  | gnd : Ground → Atom
  | expr : List Atom → Atom
  deriving Repr, Inhabited

mutual
/-- Constructor-directed Boolean comparison, reducible on structural inputs.
Floating payloads retain their IEEE Boolean comparison. This is not a claim of
lawful propositional equality or a language's numeric matching policy. -/
def Atom.beq : Atom → Atom → Bool
  | Atom.sym a, Atom.sym b => a == b
  | Atom.var a, Atom.var b => a == b
  | Atom.gnd a, Atom.gnd b => Ground.beq a b
  | Atom.expr a, Atom.expr b => Atom.beqList a b
  | _, _ => false
/-- Pointwise structural equality of atom lists (companion to `Atom.beq`). -/
def Atom.beqList : List Atom → List Atom → Bool
  | [], [] => true
  | x :: xs, y :: ys => Atom.beq x y && Atom.beqList xs ys
  | _, _ => false
end

instance : BEq Atom := ⟨Atom.beq⟩

namespace Atom

/-- Structural size: leaves count 1, an expression is `1 +` the sizes of its children. Used as the
    well-founded measure for recursion/termination over atoms. -/
def size : Atom → Nat
  | Atom.sym _ => 1
  | Atom.var _ => 1
  | Atom.gnd _ => 1
  | Atom.expr xs => 1 + (xs.map size).sum

/-- All variable occurrences in `a`, left-to-right with duplicates. Atoms have no binders, so
    every occurrence is free; see `FreeVars.lean` for the named notion used in the metatheory. -/
def vars : Atom → List VarName
  | Atom.var x => [x]
  | Atom.expr xs => (xs.map vars).flatten
  | _ => []

end Atom
end Metta
