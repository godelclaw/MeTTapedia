import MettapediaFourColor.ExecutableConfiguration

/-!
# Finite tables for embedded configuration maps

Table entries are encoded as bytes above a specified base (by default `A`).
Larger tables can use a lower ASCII base while retaining one byte per entry.
A table defines a hypermap
only after its triangular cancellation law is proved. Equality with a
construction-program map is a separate obligation, preserving all three
permutations rather than only graph adjacency.
-/

namespace FourColor.ConfigurationTable

def entryBase (base : ℕ) (s : String) (i : ℕ) : ℕ :=
  (s.toUTF8[i]?.getD (UInt8.ofNat base)).toNat - base

def entry (s : String) (i : ℕ) : ℕ := entryBase 65 s i

def lookupBase {m n : ℕ} [NeZero n] (base : ℕ) (s : String) (i : Fin m) : Fin n :=
  ⟨entryBase base s i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩

def lookup {m n : ℕ} [NeZero n] (s : String) (i : Fin m) : Fin n :=
  lookupBase 65 s i

structure Data (n : ℕ) [NeZero n] where
  base : ℕ := 65
  edges : String
  nodes : String
  faces : String
  cancel : ∀ x : Fin n,
    lookupBase base nodes (lookupBase base faces (lookupBase base edges x : Fin n) : Fin n) = x

def Data.map {n : ℕ} [NeZero n] (t : Data n) : Hypermap (Fin n) :=
  ExecutableConfiguration.ofCancel3 (lookupBase t.base t.edges) (lookupBase t.base t.nodes)
    (lookupBase t.base t.faces) t.cancel

/-- The finite check compares the entire embedded map. -/
theorem Data.eq_of_tables {n : ℕ} [NeZero n] (t : Data n) (G : Hypermap (Fin n))
    (h : ∀ x, G.edge x = lookupBase t.base t.edges x ∧
      G.node x = lookupBase t.base t.nodes x ∧
      G.face x = lookupBase t.base t.faces x) : G = t.map :=
  Hypermap.ext (Equiv.ext fun x => (h x).1) (Equiv.ext fun x => (h x).2.1)
    (Equiv.ext fun x => (h x).2.2)

end FourColor.ConfigurationTable
