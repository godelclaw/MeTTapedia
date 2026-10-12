import Mettapedia.OSLF.NativeTypes.Certificates.NativeSyntaxCoding

/-!
# Scoped coding of ordered native assumption occurrences

Duplicate assumptions keep distinct paths. Crossing a variable binder stores
the original predicate, then checks its actual weakening against the requested
predicate. Decoding never invents membership from predicate agreement alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.NativeWire

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

variable {S : Symbols} (symbols : SymbolCodecs S)

def putHypothesis : {n : Nat} → {context : ContextExpr S n} → {predicate : PropExpr S n} →
    Hypothesis context predicate → Data
  | _, _, _, .here _ _ => .atom 0
  | _, _, _, .assumptionThere member _ => .pair (.atom 1) (putHypothesis member)
  | _, _, _, @Hypothesis.variableThere _ _ _ predicate member _ =>
      .pair (.atom 2) (.pair (putProp symbols predicate) (putHypothesis member))

def getHypothesis : {n : Nat} → (context : ContextExpr S n) → (predicate : PropExpr S n) →
    Data → Option (Hypothesis context predicate)
  | n, .assume context actual, predicate, .atom 0 =>
      letI : DecidableEq (PropExpr S n) := (propAt symbols n).decEq
      if same : actual = predicate then some (same ▸ Hypothesis.here context actual) else none
  | _, .assume context actual, predicate, .pair (.atom 1) member => do
      return .assumptionThere (← getHypothesis context predicate member) actual
  | _, @ContextExpr.snoc _ n context type, predicate, .pair (.atom 2) (.pair original member) => do
      let original ← getProp symbols n original
      letI : DecidableEq (PropExpr S (n + 1)) := (propAt symbols (n + 1)).decEq
      if same : original.rename Fin.succ = predicate then
        return same ▸ Hypothesis.variableThere (← getHypothesis context original member) type
      else none
  | _, _, _, _ => none

theorem get_putHypothesis : {n : Nat} → {context : ContextExpr S n} → {predicate : PropExpr S n} →
    (member : Hypothesis context predicate) →
    getHypothesis symbols context predicate (putHypothesis symbols member) = some member
  | _, _, _, .here _ _ => by simp only [putHypothesis, getHypothesis, dite_true]
  | _, _, _, .assumptionThere member _ => by
      simp only [putHypothesis, getHypothesis, get_putHypothesis member]
      rfl
  | _, _, _, .variableThere member _ => by
      simp only [putHypothesis, getHypothesis, get_putProp, Bind.bind, Option.bind, dite_true,
        get_putHypothesis member]
      rfl

def hypothesisAt {n : Nat} (context : ContextExpr S n) (predicate : PropExpr S n) :
    Codec (Hypothesis context predicate) :=
  ⟨putHypothesis symbols, getHypothesis symbols context predicate, get_putHypothesis symbols⟩

end Mettapedia.OSLF.NativeTypes.Certificates.NativeWire
