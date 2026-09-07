import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Simple directed routes and their integral augmentation matrices

Remove loops from a finite directed route without changing its endpoints.
The signed incidence matrix of the resulting simple route has divergence
one at the start, minus one at the finish, and zero elsewhere. Each entry
is at most one; a positive entry can occur only on an allowed directed
edge. These are the exact properties needed for integer residual flow.
-/

namespace Mettapedia.GraphTheory.FourColor.IntegralFlow

universe u
variable {V : Type u} {r : V → V → Prop}

inductive Route (r : V → V → Prop) : V → V → Type u
  | nil (v : V) : Route r v v
  | cons {a b c : V} (edge : r a b) (tail : Route r b c) : Route r a c

namespace Route

def map {s : V → V → Prop} (h : ∀ a b, r a b → s a b) {a b : V} :
    Route r a b → Route s a b
  | .nil a => .nil a
  | .cons edge p => .cons (h _ _ edge) (map h p)

def support {a b : V} : Route r a b → List V
  | .nil a => [a]
  | @cons _ _ a _ _ _ p => a :: support p

@[simp] theorem support_map {s : V → V → Prop} (h : ∀ a b, r a b → s a b)
    {a b : V} (p : Route r a b) : (p.map h).support = p.support := by
  induction p <;> simp_all [map, support]

theorem start_mem {a b : V} (p : Route r a b) : a ∈ p.support := by
  cases p <;> simp [support]

theorem end_mem {a b : V} (p : Route r a b) : b ∈ p.support := by
  induction p with
  | nil => simp [support]
  | cons _ _ ih => exact List.mem_cons_of_mem _ ih

/-- A directed edge occurs as an actual consecutive step of the route. -/
def Uses {a b : V} : Route r a b → V → V → Prop
  | .nil _, _, _ => False
  | @cons _ _ a b _ _ p, u, v => (u = a ∧ v = b) ∨ Uses p u v

theorem uses_endpoints {a b u v : V} (p : Route r a b) (h : p.Uses u v) :
    u ∈ p.support ∧ v ∈ p.support := by
  induction p with
  | nil => exact h.elim
  | @cons a b c e p ih =>
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ p.start_mem⟩
    · obtain ⟨hu, hv⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hu, List.mem_cons_of_mem _ hv⟩

/-- Take a suffix beginning at any vertex already visited. -/
theorem suffix {a b x : V} (p : Route r a b) (hx : x ∈ p.support) :
    ∃ q : Route r x b, q.support.Sublist p.support := by
  induction p with
  | nil a =>
    have heq : x = a := by simpa [support] using hx
    subst x
    exact ⟨.nil a, .refl _⟩
  | @cons a c b edge p ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨.cons edge p, .refl _⟩
    · obtain ⟨q, hq⟩ := ih hx
      exact ⟨q, hq.cons _⟩

/-- Directed reachability admits a route with no repeated vertex. -/
theorem exists_simple {a b : V} (h : Relation.ReflTransGen r a b) :
    ∃ p : Route r a b, p.support.Nodup := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _, by simp [support]⟩
  | @head a c edge h ih =>
    obtain ⟨p, hp⟩ := ih
    by_cases ha : a ∈ p.support
    · obtain ⟨q, hq⟩ := p.suffix ha
      exact ⟨q, hp.sublist hq⟩
    · exact ⟨.cons edge p, by simpa [support] using List.nodup_cons.mpr ⟨ha, hp⟩⟩

variable [DecidableEq V]

/-- The signed matrix of one directed step. -/
def arc (a b u v : V) : ℤ :=
  (if u = a ∧ v = b then 1 else 0) - (if u = b ∧ v = a then 1 else 0)

def delta {a b : V} : Route r a b → V → V → ℤ
  | .nil _, _, _ => 0
  | @cons _ _ a b _ _ p, u, v => arc a b u v + delta p u v

@[simp] theorem delta_map {s : V → V → Prop} (h : ∀ a b, r a b → s a b)
    {a b : V} (p : Route r a b) (u v : V) : (p.map h).delta u v = p.delta u v := by
  induction p <;> simp_all [map, delta]

theorem arc_skew (a b u v : V) : arc a b u v = -arc a b v u := by
  simp only [arc]
  simp only [and_comm]
  omega

theorem delta_skew {a b : V} (p : Route r a b) (u v : V) :
    p.delta u v = -p.delta v u := by
  induction p with
  | nil => simp [delta]
  | @cons a b c edge p ih =>
    change arc a b u v + p.delta u v = -(arc a b v u + p.delta v u)
    rw [arc_skew a b u v, ih]
    omega

theorem delta_zero_of_not_mem {a b : V} (p : Route r a b) {u : V}
    (hu : u ∉ p.support) (v : V) : p.delta u v = 0 := by
  induction p with
  | nil => rfl
  | @cons a b c edge p ih =>
    have ha : u ≠ a := by intro h; subst u; exact hu (List.mem_cons_self ..)
    have ht : u ∉ p.support := fun h => hu (List.mem_cons_of_mem a h)
    have hb : u ≠ b := fun h => ht (h ▸ p.start_mem)
    simp [delta, arc, ha, hb, ih ht]

/-- In a simple route an occurring edge contributes exactly one unit. -/
theorem delta_eq_one_of_uses {a b u v : V} (p : Route r a b)
    (hp : p.support.Nodup) (h : p.Uses u v) : p.delta u v = 1 := by
  induction p with
  | nil => exact h.elim
  | @cons a b c e p ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hp
    rcases h with ⟨rfl, rfl⟩ | h
    · have hab : u ≠ v := fun heq => ha (heq ▸ p.start_mem)
      rw [delta, p.delta_zero_of_not_mem ha v]
      simp [arc, hab]
    · obtain ⟨hu, hv⟩ := p.uses_endpoints h
      have hua : u ≠ a := fun heq => ha (heq ▸ hu)
      have hva : v ≠ a := fun heq => ha (heq ▸ hv)
      simp [delta, arc, hua, hva, ih ht h]

theorem delta_le_one {a b : V} (p : Route r a b) (hp : p.support.Nodup) (u v : V) :
    p.delta u v ≤ 1 := by
  induction p with
  | nil => simp [delta]
  | @cons a b c edge p ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hp
    by_cases huv : u = a ∧ v = b
    · obtain ⟨rfl, rfl⟩ := huv
      rw [delta, delta_zero_of_not_mem p ha v]
      simp only [arc, true_and, ite_true, add_zero]
      split_ifs <;> omega
    · have he : arc a b u v ≤ 0 := by simp only [arc, huv, ite_false]; split_ifs <;> omega
      have htail := ih ht
      change arc a b u v + p.delta u v ≤ 1
      omega

/-- Positivity cannot be manufactured on a forbidden directed edge. -/
theorem delta_nonpos_of_not_rel {a b : V} (p : Route r a b) (u v : V)
    (h : ¬ r u v) : p.delta u v ≤ 0 := by
  induction p with
  | nil => simp [delta]
  | @cons a b c edge p ih =>
    have huv : ¬ (u = a ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact h edge
    have he : arc a b u v ≤ 0 := by simp only [arc, huv, ite_false]; split_ifs <;> omega
    change arc a b u v + p.delta u v ≤ 0
    omega

variable [Fintype V]

theorem sum_arc (a b u : V) :
    ∑ v, arc a b u v = (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  have h (x y : V) : (∑ v, if u = x ∧ v = y then (1 : ℤ) else 0) =
      (if u = x then 1 else 0) := by
    by_cases hx : u = x <;> simp [hx]
  simp only [arc, Finset.sum_sub_distrib, h]

/-- Internal route vertices have zero net augmentation. -/
theorem sum_delta {a b : V} (p : Route r a b) (u : V) :
    ∑ v, p.delta u v = (if u = a then 1 else 0) - (if u = b then 1 else 0) := by
  induction p with
  | nil => simp [delta]
  | cons edge p ih =>
    simp only [delta, Finset.sum_add_distrib, sum_arc, ih]
    omega

end Route
end Mettapedia.GraphTheory.FourColor.IntegralFlow
