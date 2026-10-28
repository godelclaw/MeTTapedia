import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Uncrossing two walks through a common vertex

Two walks that pass through a common vertex can exchange their tails there; the two new
walks have the same total length.  Hence the crossed pairing of their endpoints is no
farther apart than the walks are long
(`dist_add_dist_le_length_add_length_of_mem_support`), and for two geodesics through a
common vertex the crossed distances are at most the original ones
(`dist_add_dist_le_dist_add_dist_of_mem_support`).  This is the exchange step of
uncrossing arguments for families of shortest paths.
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b c d x : V}

/-- Exchanging tails at a common vertex preserves the total length. -/
theorem length_exchange_tails (p : G.Walk a b) (q : G.Walk c d) (hp : x ∈ p.support)
    (hq : x ∈ q.support) :
    ((p.takeUntil x hp).append (q.dropUntil x hq)).length +
        ((q.takeUntil x hq).append (p.dropUntil x hp)).length =
      p.length + q.length := by
  have hpl := congrArg Walk.length (p.take_spec hp)
  have hql := congrArg Walk.length (q.take_spec hq)
  simp only [Walk.length_append] at hpl hql ⊢
  omega

/-- **The crossed endpoints of two walks through a common vertex are no farther apart
than the walks are long.** -/
theorem dist_add_dist_le_length_add_length_of_mem_support (p : G.Walk a b) (q : G.Walk c d)
    (hp : x ∈ p.support) (hq : x ∈ q.support) :
    G.dist a d + G.dist c b ≤ p.length + q.length :=
  (Nat.add_le_add (dist_le _) (dist_le _)).trans_eq (length_exchange_tails p q hp hq)

/-- **Uncrossing geodesics.**  If shortest walks from `a` to `b` and from `c` to `d` meet,
then `dist a d + dist c b ≤ dist a b + dist c d`. -/
theorem dist_add_dist_le_dist_add_dist_of_mem_support (p : G.Walk a b) (q : G.Walk c d)
    (hp : x ∈ p.support) (hq : x ∈ q.support) (hpd : p.length = G.dist a b)
    (hqd : q.length = G.dist c d) :
    G.dist a d + G.dist c b ≤ G.dist a b + G.dist c d :=
  hpd ▸ hqd ▸ dist_add_dist_le_length_add_length_of_mem_support p q hp hq

end SimpleGraph
