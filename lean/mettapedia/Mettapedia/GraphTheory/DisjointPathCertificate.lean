import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain

/-!
# Connectivity certificates from disjoint paths

An explicit family of paths sharing only their endpoints certifies that
deleting fewer vertices than there are paths cannot separate those endpoints.
A small set of possible roots turns these local certificates into connectivity
of every induced graph obtained by deleting a bounded number of vertices.
-/

namespace Mettapedia.GraphTheory.DisjointPathCertificate

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- List form of reachability, without choosing a particular walk representation. -/
theorem reachable_of_chain (path : List V) (chain : path.IsChain G.Adj)
    {u v : V} (hu : u ∈ path) (hv : v ∈ path) : G.Reachable u v := by
  let : Trans G.Reachable G.Reachable G.Reachable := ⟨fun h k => h.trans k⟩
  have hr : path.IsChain G.Reachable := chain.imp fun _ _ h => h.reachable
  cases path with
  | nil => simp at hu
  | cons root rest =>
      have fromRoot (x : V) (hx : x ∈ root :: rest) : G.Reachable root x := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .refl _
        · exact hr.rel_cons hx
      exact (fromRoot u hu).symm.trans (fromRoot v hv)

/-- A chain contained in a vertex set remains a path in the induced graph. -/
theorem reachable_induce_of_chain (S : Set V) (path : List V)
    (chain : path.IsChain G.Adj) (inside : ∀ x ∈ path, x ∈ S)
    {u v : S} (hu : u.val ∈ path) (hv : v.val ∈ path) :
    (G.induce S).Reachable u v := by
  let lifted := path.attachWith (fun x => x ∈ S) inside
  have hc : lifted.IsChain (G.induce S).Adj := by
    apply (List.isChain_attachWith inside).mpr
    exact chain.imp_of_mem_imp fun a b ha hb hab => ⟨inside a ha, inside b hb, hab⟩
  apply reachable_of_chain (G.induce S) lifted hc
  · simpa [lifted] using hu
  · simpa [lifted] using hv

/-- The paths may repeat an endpoint, but different paths cannot share another vertex. -/
structure Family (u v : V) (k : Nat) where
  path : Fin k → List V
  start_mem : ∀ i, u ∈ path i
  finish_mem : ∀ i, v ∈ path i
  chain : ∀ i, (path i).IsChain G.Adj
  shared : ∀ i j x, i ≠ j → x ∈ path i → x ∈ path j → x = u ∨ x = v

namespace Family

variable [DecidableEq V] {G} {u v : V} {k : Nat}

/-- Fewer deleted vertices than internally disjoint paths leave a whole path intact. -/
theorem exists_avoiding (certificate : Family G u v k) (removed : Finset V)
    (bound : removed.card < k) (hu : u ∉ removed) (hv : v ∉ removed) :
    ∃ i, ∀ x ∈ certificate.path i, x ∉ removed := by
  classical
  by_contra noPath
  have hits : ∀ i, ∃ x, x ∈ removed ∧ x ∈ certificate.path i := by
    intro i
    by_contra noHit
    apply noPath
    refine ⟨i, ?_⟩
    intro x hx hremoved
    exact noHit ⟨x, hremoved, hx⟩
  choose hit hit_removed hit_path using hits
  let select : Fin k → removed := fun i => ⟨hit i, hit_removed i⟩
  have injective : Function.Injective select := by
    intro i j equal
    by_contra different
    have eq_hit : hit i = hit j := congrArg Subtype.val equal
    have shared := certificate.shared i j (hit i) different (hit_path i)
      (eq_hit ▸ hit_path j)
    rcases shared with equal | equal
    · exact hu (equal ▸ hit_removed i)
    · exact hv (equal ▸ hit_removed i)
  have cardinal := Fintype.card_le_of_injective select injective
  have hk : k ≤ removed.card := by simpa using cardinal
  exact (Nat.not_lt_of_ge hk) bound

theorem reachable_after_deleting (certificate : Family G u v k)
    (removed : Finset V) (bound : removed.card < k)
    (hu : u ∉ removed) (hv : v ∉ removed) :
    (G.induce (↑removed : Set V)ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨i, avoids⟩ := certificate.exists_avoiding removed bound hu hv
  exact reachable_induce_of_chain G (↑removed : Set V)ᶜ (certificate.path i)
    (certificate.chain i) avoids (certificate.start_mem i) (certificate.finish_mem i)

end Family

/-- An injective set of `k` possible roots contains a vertex outside every
deleted set of cardinality less than `k`. -/
theorem exists_root_outside [DecidableEq V] {k : Nat} (root : Fin k → V)
    (distinct : Function.Injective root) (removed : Finset V)
    (bound : removed.card < k) : ∃ i, root i ∉ removed := by
  classical
  by_contra noRoot
  have inside : ∀ i, root i ∈ removed := by
    intro i
    by_contra outside
    exact noRoot ⟨i, outside⟩
  let select : Fin k → removed := fun i => ⟨root i, inside i⟩
  have injective : Function.Injective select := by
    intro i j equal
    exact distinct (congrArg Subtype.val equal)
  have cardinal := Fintype.card_le_of_injective select injective
  have hk : k ≤ removed.card := by simpa using cardinal
  exact (Nat.not_lt_of_ge hk) bound

/-- Certificates from each possible root to every vertex prove connectivity
after every deletion of fewer than `k` vertices. -/
theorem connected_after_deleting [DecidableEq V] {k : Nat} (root : Fin k → V)
    (distinct : Function.Injective root)
    (certificate : ∀ i v, Family G (root i) v k)
    (removed : Finset V) (bound : removed.card < k) :
    (G.induce (↑removed : Set V)ᶜ).Connected := by
  obtain ⟨i, outside⟩ := exists_root_outside root distinct removed bound
  apply (G.induce (↑removed : Set V)ᶜ).connected_iff_exists_forall_reachable.mpr
  refine ⟨⟨root i, outside⟩, ?_⟩
  intro v
  exact (certificate i v.val).reachable_after_deleting removed bound outside v.property

end Mettapedia.GraphTheory.DisjointPathCertificate
