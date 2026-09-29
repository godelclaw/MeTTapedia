import MettapediaFourColor.KempeBoundaryMerge
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Actual triangular ears preserve boundary repair

An ear adds one new vertex adjacent to the ends of a retained boundary edge.
Its complete colouring relation is the joint boundary split. Consequently a
repair of the old piece lifts to a repair of the new piece, against every
Kempe-closed exterior. Restriction and reconstruction use genuine graph
colourings. This operation differs from subdividing a triangle: the old edge
is kept, and the new vertex has no third neighbour in the old piece.
-/

namespace FourColor.BoundaryEarRepair

open Color KempeBoundarySplit

universe u
variable {V : Type u}

/-- A new boundary vertex adjacent to both ends of the retained edge. -/
def ear (G : SimpleGraph V) (u v : V) : SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y
    | none, some y => y = u ∨ y = v
    | some x, none => x = u ∨ x = v
    | none, none => False
  symm := ⟨by rintro (x | _) (y | _) h <;> first | exact G.adj_symm h | exact h⟩
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl _ h⟩

def ports (u v : V) (tail : List V) : List (Option V) :=
  some u :: none :: some v :: tail.map some

def restrict {C : Type*} {G : SimpleGraph V} {u v : V}
    (k : (ear G u v).Coloring C) : G.Coloring C :=
  .mk (fun x => k (some x)) (fun h => k.valid h)

def extend {C : Type*} {G : SimpleGraph V} {u v : V}
    (k : G.Coloring C) (fresh : C) (hu : fresh ≠ k u) (hv : fresh ≠ k v) :
    (ear G u v).Coloring C :=
  .mk (fun x => x.elim fresh k) (by
    rintro (_ | x) (_ | y) h
    · exact False.elim h
    · rcases h with rfl | rfl
      · exact hu
      · exact hv
    · rcases h with rfl | rfl
      · exact hu.symm
      · exact hv.symm
    · exact k.valid h)

@[simp] theorem restrict_extend {C : Type*} {G : SimpleGraph V} {u v : V}
    (k : G.Coloring C) (fresh : C) (hu : fresh ≠ k u) (hv : fresh ≠ k v) :
    restrict (extend k fresh hu hv) = k := rfl

private theorem sum_cancel (a b c : Color) : (a + b) + (b + c) = a + c := by
  rw [add_assoc, ← add_assoc b, add_self, zero_add]

private theorem trace_ear (k : Option V → Color) (u v : V) (tail : List V) :
    trace ((ports u v tail).map k) =
      (k (some u) + k none) :: (k none + k (some v)) ::
        pairmap (· + ·) (k (some v)) ((tail.map fun x => k (some x)) ++ [k (some u)]) := by
  simp only [ports, List.map_cons, List.map_map, trace_cons, List.cons_append, pairmap_cons]
  rfl

/-- Elimination retains the pair of edge colours and all old vertex colours. -/
theorem trace_exact (G : SimpleGraph V) (u v : V) (tail : List V) (edge : G.Adj u v)
    (et : List Color) :
    GraphTrace (ear G u v) (ports u v tail) et ↔
      Split (GraphTrace G (u :: v :: tail)) et := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k (some u) + k none, k none + k (some v),
      pairmap (· + ·) (k (some v)) ((tail.map fun x => k (some x)) ++ [k (some u)]),
      trace_ear k u v tail, ?_, ?_, ?_, restrict k, ?_⟩
    · exact fun h => (k.valid (show (ear G u v).Adj (some u) none from Or.inl rfl))
        (Color.add_eq_zero_iff.mp h)
    · exact fun h => (k.valid (show (ear G u v).Adj none (some v) from Or.inr rfl))
        (Color.add_eq_zero_iff.mp h)
    · intro h
      apply (restrict k).valid edge
      change k (some u) = k (some v)
      have hsum := congrArg (fun x => x + (k none + k (some v))) h
      simpa only [sum_cancel, add_self, Color.add_eq_zero_iff] using hsum
    · rw [sum_cancel]
      simp only [List.map_cons, trace_cons, List.cons_append, pairmap_cons]
      rfl
  · rintro ⟨a, b, t, rfl, ha, hb, hab, k, hk⟩
    have hhead : a + b = k u + k v := by
      simpa only [List.map_cons, trace_cons, List.cons_append, pairmap_cons,
        List.head?_cons, Option.some.injEq] using congrArg List.head? hk
    have htail : t = pairmap (· + ·) (k v) ((tail.map k) ++ [k u]) := by
      simpa only [List.map_cons, trace_cons, List.cons_append, pairmap_cons,
        List.tail_cons] using congrArg List.tail hk
    have hfresh_u : k u + a ≠ k u := by
      intro h
      exact ha (add_left_cancel (h.trans (add_zero (k u)).symm))
    have hfresh_v : k u + a ≠ k v := by
      intro h
      have hh := hhead
      rw [← h, ← add_assoc, add_self, zero_add] at hh
      exact hb (add_left_cancel (hh.trans (add_zero a).symm))
    refine ⟨extend k (k u + a) hfresh_u hfresh_v, ?_⟩
    rw [trace_ear]
    change a :: b :: t =
      (k u + (k u + a)) :: ((k u + a) + k v) ::
        pairmap (· + ·) (k v) ((tail.map k) ++ [k u])
    have hsecond : (k u + a) + k v = b := by
      calc
        (k u + a) + k v = a + (k u + k v) := by ac_rfl
        _ = a + (a + b) := by rw [hhead]
        _ = b := by rw [← add_assoc, add_self, zero_add]
    rw [← add_assoc (k u), add_self, zero_add, hsecond, htail]

/-- A single core repair supplies all compatible colourings after adding an ear. -/
theorem repair (G : SimpleGraph V) (u v : V) (tail : List V) (edge : G.Adj u v)
    {P : List Color → Prop}
    (base : ∀ et, P et → KempeCoclosure (GraphTrace G (u :: v :: tail)) et)
    (et : List Color) (start : Split P et) :
    KempeCoclosure (GraphTrace (ear G u v) (ports u v tail)) et := by
  obtain ⟨a, b, t, rfl, ha, hb, hab, ht⟩ := start
  exact KempeBoundaryMerge.coclosure_expand
    (fun a b t ha hb hab hk => (trace_exact G u v tail edge _).mpr
      ⟨a, b, t, rfl, ha, hb, hab, hk⟩) a b t ha hb hab (base _ ht)

/-- Erasing the ear is strict on every finite graph. -/
theorem size [Finite V] : Nat.card (Option V) = Nat.card V + 1 := by
  simp

end FourColor.BoundaryEarRepair
