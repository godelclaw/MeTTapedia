import Mettapedia.Logic.LP.RuntimeTerm
import Mettapedia.Logic.LP.StandardizeApart

/-!
# SWI-compatible hashing of canonical LP runtime graphs

This is a mechanism of the one shared `Logic.LP` heap, not a Prolog resolver.
The traversal and MurmurHash2 mixing follow pinned SWI-Prolog 10.1.9
`src/pl-termhash.c` and `src/pl-hash.c`.  A language realization supplies only
the byte representation of its primitive tokens and functor names, plus the
constant used to expose the resulting unsigned 32-bit key.

The implementation is cycle-safe.  Completed shared subgraphs reuse their
hash.  A back-edge contributes SWI's `CYCLE_CONST`, and any ancestor containing
that cycle is itself represented by the same constant when consumed by its
parent.  Encountering an unbound variable returns `none`; `term_hash/2` can
therefore succeed without binding its output exactly as SWI does.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeTermHash

open RuntimeTerm

private def murmurSeed : UInt32 := 0x1a3be34a
private def murmurMultiplier : UInt32 := 0x5bd1e995
private def cycleConstant : UInt32 := 123456

private def littleEndian32 (value : UInt32) : List UInt8 := [
  value.toUInt8,
  (value >>> 8).toUInt8,
  (value >>> 16).toUInt8,
  (value >>> 24).toUInt8
]

private def littleEndian64 (value : UInt64) : List UInt8 := [
  value.toUInt8,
  (value >>> 8).toUInt8,
  (value >>> 16).toUInt8,
  (value >>> 24).toUInt8,
  (value >>> 32).toUInt8,
  (value >>> 40).toUInt8,
  (value >>> 48).toUInt8,
  (value >>> 56).toUInt8
]

private def word32 (a b c d : UInt8) : UInt32 :=
  a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) |||
    (d.toUInt32 <<< 24)

private def murmurMix (hash key : UInt32) : UInt32 :=
  let key := key * murmurMultiplier
  let key := key ^^^ (key >>> 24)
  let key := key * murmurMultiplier
  (hash * murmurMultiplier) ^^^ key

private def murmurBlocks : List UInt8 → UInt32 → UInt32
  | a :: b :: c :: d :: rest, hash =>
      murmurBlocks rest (murmurMix hash (word32 a b c d))
  | tail, hash =>
      let hash : UInt32 := match tail with
        | [a] => (hash ^^^ a.toUInt32) * murmurMultiplier
        | [a, b] =>
            (hash ^^^ a.toUInt32 ^^^ (b.toUInt32 <<< 8)) *
              murmurMultiplier
        | [a, b, c] =>
            (hash ^^^ a.toUInt32 ^^^ (b.toUInt32 <<< 8) ^^^
              (c.toUInt32 <<< 16)) * murmurMultiplier
        | _ => hash
      let hash := hash ^^^ (hash >>> 13)
      let hash := hash * murmurMultiplier
      hash ^^^ (hash >>> 15)

/-- The little-endian MurmurHashAligned2 value used by pinned SWI. -/
def murmurHashAligned2 (bytes : List UInt8) (seed : UInt32 := murmurSeed) :
    UInt32 :=
  murmurBlocks bytes (seed ^^^ UInt32.ofNat bytes.length)

/-- Primitive token kinds whose SWI byte representation is stable in the
supported source fragment. -/
inductive Primitive where
  | atom (name : String)
  | string (value : String)
  | integer (value : Int)
  | floatBits (bits : UInt64)
deriving Repr

/-- A source language supplies token encodings only.  It receives no heap,
memory, choice stack, continuation, or answer constructor. -/
structure Encoding (σ : LPSignature) where
  primitive : σ.constants → Option Primitive
  functorName : σ.functionSymbols → String
  resultConstant : UInt32 → σ.constants

inductive Error where
  | memory (error : MemoryError)
  | budgetExhausted
  | unsupportedConstant
deriving Repr

private def latinOneBytes? (value : String) : Option (List UInt8) :=
  let characters := value.toList
  if characters.all fun character => character.toNat ≤ 0xff then
    some (characters.map fun character => UInt8.ofNat character.toNat)
  else none

private def atomBytes (name : String) : List UInt8 :=
  match latinOneBytes? name with
  | some bytes => bytes
  | none => name.toList.flatMap fun character =>
      littleEndian32 (UInt32.ofNat character.toNat)

private def stringBytes (value : String) : List UInt8 :=
  match latinOneBytes? value with
  | some bytes => bytes
  | none => value.toUTF8.toList

/-- SWI stores Latin-1 atoms as one byte per character and wider atoms as
little-endian `pl_wchar_t` code points. -/
private def atomHash (name : String) : UInt32 :=
  murmurHashAligned2 (atomBytes name)

private def primitiveHashWith (seed : UInt32) : Primitive → UInt32
  | .atom name => murmurHashAligned2 (littleEndian32 (atomHash name)) seed
  | .string value => murmurHashAligned2 (stringBytes value) seed
  | .integer value =>
      murmurHashAligned2 (littleEndian64 (UInt64.ofInt value)) seed
  | .floatBits bits => murmurHashAligned2 (littleEndian64 bits) seed

private def primitiveHash (primitive : Primitive) : UInt32 :=
  primitiveHashWith murmurSeed primitive

private def functorHash (name : String) : UInt32 :=
  murmurHashAligned2 (littleEndian32 (atomHash name))

private structure Cached where
  root : Addr
  hash : UInt32
  inCycle : Bool

private def cached? (root : Addr) : List Cached → Option (UInt32 × Bool)
  | [] => none
  | entry :: rest =>
      if entry.root = root then some (entry.hash, entry.inCycle)
      else cached? root rest

private inductive NodeResult where
  | nonground
  | cycleEdge
  | primitive (value : Primitive)
  | hashed (hash : UInt32) (inCycle : Bool)

private structure HashState where
  result : NodeResult
  cache : List Cached

private structure ArgumentState where
  hash : UInt32
  inCycle : Bool
  cache : List Cached

mutual
  private def hashNode {σ : LPSignature} (encoding : Encoding σ)
      (heap : Heap σ.scoped) :
      Nat → Addr → List Addr → List Cached → Except Error HashState
    | 0, _, _, _ => .error .budgetExhausted
    | fuel + 1, address, active, cache =>
        match heap.deref address with
        | .error error => .error (.memory error)
        | .ok (.variableCycle cycle) =>
            .error (.memory (.variableReferenceCycle cycle))
        | .ok (.root root) =>
            if root ∈ active then .ok { result := .cycleEdge, cache }
            else
              match cached? root cache with
              | some (hash, inCycle) =>
                  .ok { result := .hashed hash inCycle, cache }
              | none =>
                  match heap[root]? with
                  | none => .error (.memory (.invalidAddress root))
                  | some (.var _ none) =>
                      .ok { result := .nonground, cache }
                  | some (.var _ (some _)) =>
                      .error (.memory .illFormedHeap)
                  | some (.const constant) =>
                      match encoding.primitive constant with
                      | none => .error .unsupportedConstant
                      | some primitive =>
                          .ok {
                            result := .primitive primitive
                            cache
                          }
                  | some (.app symbol arguments) => do
                      let initial := functorHash (encoding.functorName symbol)
                      let arguments ← hashArguments encoding heap fuel
                        arguments.toList (root :: active) {
                          hash := initial
                          inCycle := false
                          cache
                        }
                      match arguments with
                      | none => .ok { result := .nonground, cache := cache }
                      | some completed =>
                          .ok {
                            result := .hashed completed.hash completed.inCycle
                            cache := {
                              root
                              hash := completed.hash
                              inCycle := completed.inCycle
                            } :: completed.cache
                          }

  private def hashArguments {σ : LPSignature} (encoding : Encoding σ)
      (heap : Heap σ.scoped) (fuel : Nat) :
      List Addr → List Addr → ArgumentState →
        Except Error (Option ArgumentState)
    | [], _, state => .ok (some state)
    | child :: rest, active, state => do
        let child ← hashNode encoding heap fuel child active state.cache
        match child.result with
        | .nonground => .ok none
        | .cycleEdge =>
            hashArguments encoding heap fuel rest active {
              hash := murmurHashAligned2 (littleEndian32 cycleConstant)
                state.hash
              inCycle := true
              cache := child.cache
            }
        | .primitive primitive =>
            hashArguments encoding heap fuel rest active {
              hash := primitiveHashWith state.hash primitive
              inCycle := state.inCycle
              cache := child.cache
            }
        | .hashed hash inCycle =>
            let contribution := if inCycle then cycleConstant else hash
            hashArguments encoding heap fuel rest active {
              hash := murmurHashAligned2 (littleEndian32 contribution)
                state.hash
              inCycle := state.inCycle || inCycle
              cache := child.cache
            }
end

/-- Hash one canonical heap graph.  `none` is SWI's successful non-ground
case, in which the caller must leave the hash output untouched. -/
def hash? {σ : LPSignature} (encoding : Encoding σ) (heap : Heap σ.scoped)
    (root : Addr) : Except Error (Option UInt32) := do
  let state ← hashNode encoding heap (heap.size + 1) root [] []
  match state.result with
  | .nonground => .ok none
  | .cycleEdge => .error .budgetExhausted
  | .primitive primitive => .ok (some (primitiveHash primitive))
  | .hashed hash _ => .ok (some hash)

end RuntimeTermHash
end Mettapedia.Logic.LP
