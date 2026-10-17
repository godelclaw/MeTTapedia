import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireData
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DefinitionalExpansion

/-!
# Conversion on native wire-data images

The literal constructor encoding is pure-normal at every ambient scope.
Replacing an actually fresh checker constant leaves every encoded packet
unchanged, including payloads containing that constant's printed spelling.
Interpreting each installed root by pure conversion then reflects full ambient
conversion of two encoded packets to literal packet equality. Conversion paths
may leave the image. This is a syntactic theorem and selects no Data model,
identity principle, normalizer, or decision procedure for ambient conversion.
-/

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireDataConversion

open Presentation

variable {n : Nat} {headEq : Tower.Head → Tower.Head → Prop}

private theorem binaryConstructor_noStep (name : DeclName)
    {first last : Tower.Tm n}
    (firstNormal : ∀ {next}, Step headEq first next → False)
    (lastNormal : ∀ {next}, Step headEq last next → False) :
    ∀ {next}, Step headEq (.app (.app (.const name) first) last) next → False := by
  intro next step
  cases step with
  | root impossible => exact impossible.elim
  | congAppArg inside => exact lastNormal inside
  | congAppFun inside =>
      cases inside with
      | root impossible => exact impossible.elim
      | congAppArg inside => exact firstNormal inside
      | congAppFun inside => cases inside with | root impossible => exact impossible.elim

mutual

theorem encode_noStep (wire : NativeWireData.Wire) :
    ∀ {next}, Step headEq (NativeWireData.encode (n := n) wire) next → False := by
  intro next step
  cases wire with
  | symbol _ | string _ | natural _ =>
      simp only [NativeWireData.encode] at step
      cases step with | root impossible => exact impossible.elim
  | application head arguments =>
      apply binaryConstructor_noStep NativeWireData.applicationName
        (first := .const (.str NativeWireData.symbolPrefix head))
        (by intro next step; cases step with | root impossible => exact impossible.elim)
        (encodeList_noStep arguments)
      simpa only [NativeWireData.encode] using step
termination_by sizeOf wire

theorem encodeList_noStep (wires : List NativeWireData.Wire) :
    ∀ {next}, Step headEq (NativeWireData.encodeList (n := n) wires) next → False := by
  intro next step
  cases wires with
  | nil =>
      simp only [NativeWireData.encodeList] at step
      cases step with | root impossible => exact impossible.elim
  | cons wire wires =>
      apply binaryConstructor_noStep NativeWireData.consName
        (encode_noStep wire) (encodeList_noStep wires)
      simpa only [NativeWireData.encodeList] using step
termination_by sizeOf wires

end

/-- Freshness comes from the actual declaration lookup and the original
encoding's typing, without a separate assumption about literal payloads. -/
theorem encode_fixed_of_fresh {selected : DeclName}
    (fresh : NativeWireData.rules.constantType selected = none)
    (wire : NativeWireData.Wire) :
    ConstantExpansion.expand (ConstantExpansion.projectConstant selected)
      (NativeWireData.encode (n := n) wire) = NativeWireData.encode wire := by
  have closed : ConstantExpansion.expand (ConstantExpansion.projectConstant selected)
      (NativeWireData.encode (n := 0) wire) = NativeWireData.encode wire := by
    apply FormationSensitive.Typing.expand_eq_of_declared_constants
      (NativeWireData.encode_typing .nil wire)
    intro name declared
    have different : name ≠ selected := by
      intro same
      subst name
      exact declared fresh
    simp only [ConstantExpansion.projectConstant, different, if_false]
  have opened := congrArg (fun term : Tower.Tm 0 => rename (m := n) Fin.elim0 term) closed
  simpa only [← ConstantExpansion.expand_rename, NativeWireData.rename_encode] using opened

/-- All installed roots are interpreted, rather than just steps whose
endpoints happen to lie in the image. No source confluence premise is used. -/
theorem encode_conversion_iff_eq_of_projection (rules : Rules Tower.Head)
    (selected : DeclName) (fresh : NativeWireData.rules.constantType selected = none)
    (roots : ∀ {scope : Nat} {left right : Tower.Tm scope}, rules.computation.step left right →
      Conv rules.headEq
        (ConstantExpansion.expand (ConstantExpansion.projectConstant selected) left)
        (ConstantExpansion.expand (ConstantExpansion.projectConstant selected) right))
    (symmetric : Std.Symm rules.headEq) (first last : NativeWireData.Wire) :
    Conv rules.headEq (NativeWireData.encode (n := n) first)
      (NativeWireData.encode last) rules.computation ↔ first = last := by
  constructor
  · intro conversion
    apply NativeWireData.encode_injective (n := n)
    exact ConstantExpansion.equality_of_fixed_normal
      (ConstantExpansion.projectConstant selected) roots symmetric
      (encode_fixed_of_fresh fresh first) (encode_fixed_of_fresh fresh last)
      (encode_noStep first) (encode_noStep last) conversion
  · intro same
    cases same
    exact .refl _

#print axioms encode_noStep
#print axioms encodeList_noStep
#print axioms encode_fixed_of_fresh
#print axioms encode_conversion_iff_eq_of_projection

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireDataConversion
