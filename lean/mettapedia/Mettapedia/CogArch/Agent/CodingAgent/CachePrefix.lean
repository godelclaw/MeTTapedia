import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Prompt-prefix caching

Model providers cache requests by prefix: the part of a request that repeats
the previous request item for item is served from the cache, and only the rest
is processed again. How an agent lays out its requests therefore decides what
each step costs. One coding agent sends its world state (permissions,
environment, project instructions) once and appends changes to it as new
items, so earlier items never change; another rebuilds its system prompt
before every step.

Proved:

* the cache ends at the first changed item (`lcp_le_of_ne`), and a shared
  prefix is always served (`lcp_append_left`);
* appending only pays for what was appended (`uncached_append`);
* changing the first item pays for the whole request again
  (`uncached_head_change`);
* a layout with a part that only grows, followed by a part that may change
  every step, pays at most for the growth and the changing part
  (`uncached_layout`), so volatile content belongs at the end;
* rewriting history, as compaction does, still keeps an unchanged head served
  (`uncached_rewrite_after_head`).

Items stand for whatever the provider compares: tokens, messages or blocks.

This is the ideal of a prefix cache: `lcp` is the most any prefix cache can
serve. A deployed cache serves at most that. It reuses a prefix only at the
boundaries it caches, only above its minimum length, and only while the entry
is still held. The costs below are therefore ideal costs: a real step pays at
least as much, and a layout that is bad for the ideal cache is bad for every
cache.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Agent.CodingAgent.CachePrefix

universe u

variable {α : Type u} [DecidableEq α]

/-- The length of the longest common prefix: how much of the next request a
prefix cache serves from the previous one. -/
def lcp : List α → List α → ℕ
  | a :: as, b :: bs => if a = b then lcp as bs + 1 else 0
  | _, _ => 0

/-- The part of the next request the provider processes again. -/
def uncached (prev next : List α) : ℕ := next.length - lcp prev next

/-! ## Where the cache ends -/

theorem lcp_append_left (p x y : List α) : lcp (p ++ x) (p ++ y) = p.length + lcp x y := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [List.cons_append, lcp, ih, List.length_cons, if_true]
    omega

theorem lcp_nil_left (y : List α) : lcp [] y = 0 := by
  cases y <;> rfl

theorem lcp_self_append (l r : List α) : lcp l (l ++ r) = l.length := by
  have h := lcp_append_left l [] r
  simpa [lcp_nil_left] using h

/-- The cache ends at the first changed item. -/
theorem lcp_le_of_ne : ∀ (x y : List α) (i : ℕ) (hx : i < x.length) (hy : i < y.length),
    x[i] ≠ y[i] → lcp x y ≤ i
  | [], _, i, hx, _, _ => by simp at hx
  | _ :: _, [], i, _, hy, _ => by simp at hy
  | a :: as, b :: bs, 0, _, _, h => by
    have hab : a ≠ b := by simpa using h
    simp [lcp, hab]
  | a :: as, b :: bs, i + 1, hx, hy, h => by
    simp only [lcp]
    split
    · have := lcp_le_of_ne as bs i (by simpa using hx) (by simpa using hy) (by simpa using h)
      omega
    · omega

/-! ## What a step costs -/

/-- Appending only pays for what was appended. -/
theorem uncached_append (l r : List α) : uncached l (l ++ r) = r.length := by
  simp [uncached, lcp_self_append]

/-- Changing the first item pays for the whole request again. -/
theorem uncached_head_change (a b : α) (as bs : List α) (h : a ≠ b) :
    uncached (a :: as) (b :: bs) = bs.length + 1 := by
  simp [uncached, lcp, h]

/-- **Layout.** If the request is a part `P` that only grows (by `D`) followed by
a part that may change every step (`V`, then `V'`), a step pays at most for
the growth and the changing part. -/
theorem uncached_layout (P D V V' : List α) :
    uncached (P ++ V) (P ++ D ++ V') ≤ D.length + V'.length := by
  unfold uncached
  rw [List.append_assoc, lcp_append_left]
  simp only [List.length_append]
  omega

/-- Rewriting everything after an unchanged head, as compaction rewrites
history, still has the head served. -/
theorem uncached_rewrite_after_head (H x y : List α) :
    uncached (H ++ x) (H ++ y) ≤ y.length := by
  unfold uncached
  rw [lcp_append_left]
  simp only [List.length_append]
  omega

end Mettapedia.CogArch.Agent.CodingAgent.CachePrefix
