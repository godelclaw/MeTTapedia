import Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom
import MeTTailCore.MeTTaSyntax.Atom

/-!
# Embedding the versioned PeTTa source carrier

The historical source profile has seven grounded-payload constructors. The
shared carrier additionally supports structured binding packets. A partial
projection makes that boundary explicit, and its left-inverse laws prove that
the source embedding loses no atom data. These are representation theorems;
operational correspondence is stated by the separate reader and machine proofs.
-/

namespace Mettapedia.Languages.MeTTa.PLeaTTa.SourceEmbedding

def groundToShared : Source.Ground → _root_.Metta.Ground
  | .int value => .int value
  | .float value => .float value
  | .str value => .str value
  | .bool value => .bool value
  | .unit => .unit
  | .error value => .error value
  | .external tag payload => .external tag payload

def groundFromShared : _root_.Metta.Ground → Option Source.Ground
  | .int value => some (.int value)
  | .float value => some (.float value)
  | .str value => some (.str value)
  | .bool value => some (.bool value)
  | .unit => some .unit
  | .error value => some (.error value)
  | .external tag payload => some (.external tag payload)
  | .bindings _ => none

@[simp] theorem groundFromShared_toShared (value : Source.Ground) :
    groundFromShared (groundToShared value) = some value := by
  cases value <;> rfl

theorem binding_packet_outside_source_profile (bindings : List _root_.Metta.StoredBinding) :
    groundFromShared (.bindings bindings) = none := rfl

mutual
  def atomToShared : Source.Atom → _root_.Metta.Atom
    | .sym name => .sym name
    | .var name => .var name
    | .gnd value => .gnd (groundToShared value)
    | .expr children => .expr (atomsToShared children)

  def atomsToShared : List Source.Atom → List _root_.Metta.Atom
    | [] => []
    | atom :: atoms => atomToShared atom :: atomsToShared atoms
end

mutual
  def atomFromShared : _root_.Metta.Atom → Option Source.Atom
    | .sym name => some (.sym name)
    | .var name => some (.var name)
    | .gnd value => (groundFromShared value).map Source.Atom.gnd
    | .expr children => (atomsFromShared children).map Source.Atom.expr

  def atomsFromShared : List _root_.Metta.Atom → Option (List Source.Atom)
    | [] => some []
    | atom :: atoms => do
        let head ← atomFromShared atom
        let tail ← atomsFromShared atoms
        pure (head :: tail)
end

mutual
  @[simp] theorem atomFromShared_toShared : ∀ atom : Source.Atom,
      atomFromShared (atomToShared atom) = some atom
    | .sym _ => rfl
    | .var _ => rfl
    | .gnd value => by
        simp only [atomToShared, atomFromShared, groundFromShared_toShared, Option.map_some]
    | .expr children => by
        simp only [atomToShared, atomFromShared, atomsFromShared_toShared, Option.map_some]

  @[simp] theorem atomsFromShared_toShared : ∀ atoms : List Source.Atom,
      atomsFromShared (atomsToShared atoms) = some atoms
    | [] => rfl
    | atom :: atoms => by
        simp only [atomsToShared, atomsFromShared, atomFromShared_toShared,
          atomsFromShared_toShared]
        rfl
end

theorem atomToShared_injective : Function.Injective atomToShared := by
  intro left right same
  have projected := congrArg atomFromShared same
  simpa only [atomFromShared_toShared, Option.some.injEq] using projected

theorem groundToShared_injective : Function.Injective groundToShared := by
  intro left right same
  have projected := congrArg groundFromShared same
  simpa only [groundFromShared_toShared, Option.some.injEq] using projected

end Mettapedia.Languages.MeTTa.PLeaTTa.SourceEmbedding
