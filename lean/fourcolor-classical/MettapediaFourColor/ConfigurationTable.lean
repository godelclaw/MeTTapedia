import MettapediaFourColor.ExecutableConfiguration

/-!
# Finite tables for embedded configuration maps

Table entries are encoded as bytes starting at `A`. A table defines a hypermap
only after its triangular cancellation law is proved. Equality with a
construction-program map is a separate obligation, preserving all three
permutations rather than only graph adjacency.
-/

namespace FourColor.ConfigurationTable

def entry (s : String) (i : ℕ) : ℕ := (s.toUTF8[i]?.getD 65).toNat - 65

def lookup {m n : ℕ} [NeZero n] (s : String) (i : Fin m) : Fin n :=
  ⟨entry s i.val % n, Nat.mod_lt _ (NeZero.pos n)⟩

structure Data (n : ℕ) [NeZero n] where
  edges : String
  nodes : String
  faces : String
  cancel : ∀ x : Fin n,
    lookup nodes (lookup faces (lookup edges x : Fin n) : Fin n) = x

def Data.map {n : ℕ} [NeZero n] (t : Data n) : Hypermap (Fin n) :=
  ExecutableConfiguration.ofCancel3 (lookup t.edges) (lookup t.nodes)
    (lookup t.faces) t.cancel

/-- The finite check compares the entire embedded map. -/
theorem Data.eq_of_tables {n : ℕ} [NeZero n] (t : Data n) (G : Hypermap (Fin n))
    (h : ∀ x, G.edge x = lookup t.edges x ∧ G.node x = lookup t.nodes x ∧
      G.face x = lookup t.faces x) : G = t.map :=
  Hypermap.ext (Equiv.ext fun x => (h x).1) (Equiv.ext fun x => (h x).2.1)
    (Equiv.ext fun x => (h x).2.2)

end FourColor.ConfigurationTable
