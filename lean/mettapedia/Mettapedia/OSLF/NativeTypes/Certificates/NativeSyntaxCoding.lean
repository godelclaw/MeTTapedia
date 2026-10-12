import Mettapedia.OSLF.Syntax.BindingWireData
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementDecidableSyntax
import Mathlib.Tactic.DeriveEncodable

/-!
# Complete scoped native syntax wire representation

This codec represents the existing dependent grammar, rather than declaring a
second grammar. Primitive codes, all annotations, bound indices and ordered
arguments survive exact decoding. Decoding checks each requested scope.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.NativeWire

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

structure SymbolCodecs (S : Symbols) where
  typeSymbol : Codec S.TypeSymbol
  termSymbol : Codec S.TermSymbol
  predicateSymbol : Codec S.PredicateSymbol

variable {S : Symbols} (symbols : SymbolCodecs S)

def putDataList : List Data → Data
  | [] => .atom 0
  | head :: tail => .pair head (putDataList tail)

mutual
def putType : {n : Nat} → TypeExpr S n → Data
  | _, .family symbol arguments => .pair (.atom 0) (.pair (symbols.typeSymbol.put symbol)
      (putDataList (List.ofFn (fun position => putTerm (arguments position)))))
  | _, .propositions => .pair (.atom 1) (.atom 0)
  | _, .pi a b => .pair (.atom 2) (.pair (putType a) (.pair (putType b) (.atom 0)))
  | _, .sigma a b => .pair (.atom 3) (.pair (putType a) (.pair (putType b) (.atom 0)))
  | _, .comprehension a b => .pair (.atom 4) (.pair (putType a) (.pair (putProp b) (.atom 0)))
def putTerm : {n : Nat} → TermExpr S n → Data
  | _, .primitive symbol arguments => .pair (.atom 0) (.pair (symbols.termSymbol.put symbol)
      (putDataList (List.ofFn (fun position => putTerm (arguments position)))))
  | _, .var i => .pair (.atom 1) (.pair (.atom i.val) (.atom 0))
  | _, .lam a b c => .pair (.atom 2) (.pair (putType a) (.pair (putType b) (.pair (putTerm c) (.atom 0))))
  | _, .app a b c d => .pair (.atom 3) (.pair (putType a) (.pair (putType b) (.pair (putTerm c) (.pair (putTerm d) (.atom 0)))))
  | _, .pair a b c d => .pair (.atom 4) (.pair (putType a) (.pair (putType b) (.pair (putTerm c) (.pair (putTerm d) (.atom 0)))))
  | _, .fst a b c => .pair (.atom 5) (.pair (putType a) (.pair (putType b) (.pair (putTerm c) (.atom 0))))
  | _, .snd a b c => .pair (.atom 6) (.pair (putType a) (.pair (putType b) (.pair (putTerm c) (.atom 0))))
  | _, .sigmaElim a b c d e => .pair (.atom 7) (.pair (putType a) (.pair (putType b) (.pair (putType c) (.pair (putTerm d) (.pair (putTerm e) (.atom 0))))))
  | _, .quote a => .pair (.atom 8) (.pair (putProp a) (.atom 0))
  | _, .refine a b c => .pair (.atom 9) (.pair (putType a) (.pair (putProp b) (.pair (putTerm c) (.atom 0))))
  | _, .forget a b c => .pair (.atom 10) (.pair (putType a) (.pair (putProp b) (.pair (putTerm c) (.atom 0))))
def putProp : {n : Nat} → PropExpr S n → Data
  | _, .atom symbol arguments => .pair (.atom 0) (.pair (symbols.predicateSymbol.put symbol)
      (putDataList (List.ofFn (fun position => putTerm (arguments position)))))
  | _, .truth => .pair (.atom 1) (.atom 0)
  | _, .falsehood => .pair (.atom 2) (.atom 0)
  | _, .and a b => .pair (.atom 3) (.pair (putProp a) (.pair (putProp b) (.atom 0)))
  | _, .or a b => .pair (.atom 4) (.pair (putProp a) (.pair (putProp b) (.atom 0)))
  | _, .implies a b => .pair (.atom 5) (.pair (putProp a) (.pair (putProp b) (.atom 0)))
  | _, .all a b => .pair (.atom 6) (.pair (putType a) (.pair (putProp b) (.atom 0)))
  | _, .exists a b => .pair (.atom 7) (.pair (putType a) (.pair (putProp b) (.atom 0)))
  | _, .holds a => .pair (.atom 8) (.pair (putTerm a) (.atom 0))
  | _, .image a => .pair (.atom 9) (.pair (putType a) (.atom 0))
end

mutual
def getType (n : Nat) : Data → Option (TypeExpr S n)
  | .pair (.atom 0) (.pair symbol arguments) => do
      let symbol ← symbols.typeSymbol.get symbol
      return .family symbol (← getArguments n (S.typeArity symbol) arguments)
  | .pair (.atom 1) (.atom 0) => some .propositions
  | .pair (.atom 2) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      return .pi a b
  | .pair (.atom 3) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      return .sigma a b
  | .pair (.atom 4) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getType n a
      let b ← getProp (n + 1) b
      return .comprehension a b
  | _ => none
def getTerm (n : Nat) : Data → Option (TermExpr S n)
  | .pair (.atom 0) (.pair symbol arguments) => do
      let symbol ← symbols.termSymbol.get symbol
      return .primitive symbol (← getArguments n (S.termArity symbol) arguments)
  | .pair (.atom 1) (.pair (i) (.atom 0)) => do
      let i ← (Codec.fin n).get i
      return .var i
  | .pair (.atom 2) (.pair (a) (.pair (b) (.pair (c) (.atom 0)))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getTerm (n + 1) c
      return .lam a b c
  | .pair (.atom 3) (.pair (a) (.pair (b) (.pair (c) (.pair (d) (.atom 0))))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getTerm n c
      let d ← getTerm n d
      return .app a b c d
  | .pair (.atom 4) (.pair (a) (.pair (b) (.pair (c) (.pair (d) (.atom 0))))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getTerm n c
      let d ← getTerm n d
      return .pair a b c d
  | .pair (.atom 5) (.pair (a) (.pair (b) (.pair (c) (.atom 0)))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getTerm n c
      return .fst a b c
  | .pair (.atom 6) (.pair (a) (.pair (b) (.pair (c) (.atom 0)))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getTerm n c
      return .snd a b c
  | .pair (.atom 7) (.pair (a) (.pair (b) (.pair (c) (.pair (d) (.pair (e) (.atom 0)))))) => do
      let a ← getType n a
      let b ← getType (n + 1) b
      let c ← getType (n + 1) c
      let d ← getTerm (n + 2) d
      let e ← getTerm n e
      return .sigmaElim a b c d e
  | .pair (.atom 8) (.pair (a) (.atom 0)) => do
      let a ← getProp n a
      return .quote a
  | .pair (.atom 9) (.pair (a) (.pair (b) (.pair (c) (.atom 0)))) => do
      let a ← getType n a
      let b ← getProp (n + 1) b
      let c ← getTerm n c
      return .refine a b c
  | .pair (.atom 10) (.pair (a) (.pair (b) (.pair (c) (.atom 0)))) => do
      let a ← getType n a
      let b ← getProp (n + 1) b
      let c ← getTerm n c
      return .forget a b c
  | _ => none
def getProp (n : Nat) : Data → Option (PropExpr S n)
  | .pair (.atom 0) (.pair symbol arguments) => do
      let symbol ← symbols.predicateSymbol.get symbol
      return .atom symbol (← getArguments n (S.predicateArity symbol) arguments)
  | .pair (.atom 1) (.atom 0) => some .truth
  | .pair (.atom 2) (.atom 0) => some .falsehood
  | .pair (.atom 3) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getProp n a
      let b ← getProp n b
      return .and a b
  | .pair (.atom 4) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getProp n a
      let b ← getProp n b
      return .or a b
  | .pair (.atom 5) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getProp n a
      let b ← getProp n b
      return .implies a b
  | .pair (.atom 6) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getType n a
      let b ← getProp (n + 1) b
      return .all a b
  | .pair (.atom 7) (.pair (a) (.pair (b) (.atom 0))) => do
      let a ← getType n a
      let b ← getProp (n + 1) b
      return .exists a b
  | .pair (.atom 8) (.pair (a) (.atom 0)) => do
      let a ← getTerm n a
      return .holds a
  | .pair (.atom 9) (.pair (a) (.atom 0)) => do
      let a ← getType n a
      return .image a
  | _ => none
def getArguments (n : Nat) : (k : Nat) → Data → Option (Fin k → TermExpr S n)
  | 0, .atom 0 => some Fin.elim0
  | k + 1, .pair head tail => do
      let first ← getTerm n head
      let remaining ← getArguments n k tail
      return Fin.cases first remaining
  | _, _ => none
end

 theorem getArguments_put (n k : Nat) (arguments : Fin k → TermExpr S n)
    (roundtrip : ∀ position, getTerm symbols n (putTerm symbols (arguments position)) = some (arguments position)) :
    getArguments symbols n k (putDataList (List.ofFn (fun position => putTerm symbols (arguments position)))) = some arguments := by
  induction k with
  | zero =>
      have same : arguments = Fin.elim0 := by funext position; exact Fin.elim0 position
      subst arguments
      rfl
  | succ k ih =>
      rw [List.ofFn_succ]
      change (do
        let first ← getTerm symbols n (putTerm symbols (arguments 0))
        let remaining ← getArguments symbols n k
          (putDataList (List.ofFn (fun position => putTerm symbols (arguments position.succ))))
        return Fin.cases first remaining) = some arguments
      rw [roundtrip 0, ih (fun position => arguments position.succ) (fun position => roundtrip position.succ)]
      simp only [Bind.bind, Option.bind, pure, Pure.pure]
      congr 1
      funext position
      cases position using Fin.cases <;> rfl

mutual
theorem get_putType : {n : Nat} → (value : TypeExpr S n) →
    getType symbols n (putType symbols value) = some value
  | _, .family symbol arguments => by
      simp only [putType, getType, symbols.typeSymbol.get_put, Bind.bind, Option.bind]
      rw [getArguments_put symbols _ _ arguments (fun position => get_putTerm (arguments position))]
      rfl
  | _, .propositions => by
      simp only [putType, getType]
  | _, .pi a b => by
      simp only [putType, getType, get_putType a, get_putType b]
      rfl
  | _, .sigma a b => by
      simp only [putType, getType, get_putType a, get_putType b]
      rfl
  | _, .comprehension a b => by
      simp only [putType, getType, get_putType a, get_putProp b]
      rfl
theorem get_putTerm : {n : Nat} → (value : TermExpr S n) →
    getTerm symbols n (putTerm symbols value) = some value
  | _, .primitive symbol arguments => by
      simp only [putTerm, getTerm, symbols.termSymbol.get_put, Bind.bind, Option.bind]
      rw [getArguments_put symbols _ _ arguments (fun position => get_putTerm (arguments position))]
      rfl
  | _, .var i => by
      change (do
        let index ← (Codec.fin _).get ((Codec.fin _).put i)
        return TermExpr.var index) = some (TermExpr.var i)
      rw [Codec.get_put]
      rfl
  | _, .lam a b c => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putTerm c]
      rfl
  | _, .app a b c d => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putTerm c, get_putTerm d]
      rfl
  | _, .pair a b c d => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putTerm c, get_putTerm d]
      rfl
  | _, .fst a b c => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putTerm c]
      rfl
  | _, .snd a b c => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putTerm c]
      rfl
  | _, .sigmaElim a b c d e => by
      simp only [putTerm, getTerm, get_putType a, get_putType b, get_putType c, get_putTerm d, get_putTerm e]
      rfl
  | _, .quote a => by
      simp only [putTerm, getTerm, get_putProp a]
      rfl
  | _, .refine a b c => by
      simp only [putTerm, getTerm, get_putType a, get_putProp b, get_putTerm c]
      rfl
  | _, .forget a b c => by
      simp only [putTerm, getTerm, get_putType a, get_putProp b, get_putTerm c]
      rfl
theorem get_putProp : {n : Nat} → (value : PropExpr S n) →
    getProp symbols n (putProp symbols value) = some value
  | _, .atom symbol arguments => by
      simp only [putProp, getProp, symbols.predicateSymbol.get_put, Bind.bind, Option.bind]
      rw [getArguments_put symbols _ _ arguments (fun position => get_putTerm (arguments position))]
      rfl
  | _, .truth => by
      simp only [putProp, getProp]
  | _, .falsehood => by
      simp only [putProp, getProp]
  | _, .and a b => by
      simp only [putProp, getProp, get_putProp a, get_putProp b]
      rfl
  | _, .or a b => by
      simp only [putProp, getProp, get_putProp a, get_putProp b]
      rfl
  | _, .implies a b => by
      simp only [putProp, getProp, get_putProp a, get_putProp b]
      rfl
  | _, .all a b => by
      simp only [putProp, getProp, get_putType a, get_putProp b]
      rfl
  | _, .exists a b => by
      simp only [putProp, getProp, get_putType a, get_putProp b]
      rfl
  | _, .holds a => by
      simp only [putProp, getProp, get_putTerm a]
      rfl
  | _, .image a => by
      simp only [putProp, getProp, get_putType a]
      rfl
end

def typeAt (n : Nat) : Codec (TypeExpr S n) :=
  ⟨putType symbols, getType symbols n, get_putType symbols⟩

def termAt (n : Nat) : Codec (TermExpr S n) :=
  ⟨putTerm symbols, getTerm symbols n, get_putTerm symbols⟩

def propAt (n : Nat) : Codec (PropExpr S n) :=
  ⟨putProp symbols, getProp symbols n, get_putProp symbols⟩

def putContext : {n : Nat} → ContextExpr S n → Data
  | _, .nil => .pair (.atom 0) (.atom 0)
  | _, .snoc context type => .pair (.atom 1) (.pair (putContext context) (putType symbols type))
  | _, .assume context predicate => .pair (.atom 2) (.pair (putContext context) (putProp symbols predicate))

def getContext : (n : Nat) → Data → Option (ContextExpr S n)
  | 0, .pair (.atom 0) (.atom 0) => some .nil
  | n + 1, .pair (.atom 1) (.pair context type) => do
      return .snoc (← getContext n context) (← getType symbols n type)
  | n, .pair (.atom 2) (.pair context predicate) => do
      return .assume (← getContext n context) (← getProp symbols n predicate)
  | _, _ => none

theorem get_putContext : {n : Nat} → (context : ContextExpr S n) →
    getContext symbols n (putContext symbols context) = some context
  | _, .nil => rfl
  | _, .snoc context type => by
      simp only [putContext, getContext, get_putContext context, get_putType symbols type]
      rfl
  | _, .assume context predicate => by
      simp only [putContext, getContext, get_putContext context, get_putProp symbols predicate]
      rfl

def contextAt (n : Nat) : Codec (ContextExpr S n) :=
  ⟨putContext symbols, getContext symbols n, get_putContext symbols⟩

def argumentsAt (n k : Nat) : Codec (Fin k → TermExpr S n) :=
  ⟨fun arguments => putDataList (List.ofFn (fun position => putTerm symbols (arguments position))),
    getArguments symbols n k,
    fun arguments => getArguments_put symbols n k arguments
      (fun position => get_putTerm symbols (arguments position))⟩

end Mettapedia.OSLF.NativeTypes.Certificates.NativeWire
