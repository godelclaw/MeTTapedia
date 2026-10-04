import MettapediaFourColor.KempeBoundaryFan

/-!
# Actual graph colourings under boundary fan growth

A new boundary vertex is adjacent to three consecutive old boundary
vertices. The old middle vertex moves into the interior. Two facial
triangles fill the region between the old and new paths. The theorem below
concerns graph colourings and repair relations; embedding and occurrence
supply are separate obligations for an ambient-map consumer.
-/

namespace FourColor.BoundaryFanRepair

open Color KempeBoundarySplit KempeBoundaryFan

variable {V : Type*}

def grow (G : SimpleGraph V) (u m v : V) : SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y
    | none, some y => y = u ∨ y = m ∨ y = v
    | some x, none => x = u ∨ x = m ∨ x = v
    | none, none => False
  symm := ⟨by rintro (x | _) (y | _) h <;> first | exact G.adj_symm h | exact h⟩
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl _ h⟩

def oldPorts (u m v : V) (tail : List V) := u :: m :: v :: tail
def newPorts (u v : V) (tail : List V) := some u :: none :: some v :: tail.map some

def restrict {G : SimpleGraph V} {u m v : V} {C : Type*}
    (k : (grow G u m v).Coloring C) : G.Coloring C :=
  .mk (fun x => k (some x)) (fun h => k.valid h)

def extend {G : SimpleGraph V} {u m v : V} {C : Type*}
    (k : G.Coloring C) (fresh : C)
    (hu : fresh ≠ k u) (hm : fresh ≠ k m) (hv : fresh ≠ k v) :
    (grow G u m v).Coloring C :=
  .mk (fun x => x.elim fresh k) (by
    rintro (_ | x) (_ | y) h
    · exact False.elim h
    · rcases h with rfl | rfl | rfl
      · exact hu
      · exact hm
      · exact hv
    · rcases h with rfl | rfl | rfl
      · exact hu.symm
      · exact hm.symm
      · exact hv.symm
    · exact k.valid h)

private theorem vertex_relation : ∀ u m v fresh : Color,
    u ≠ m → m ≠ v → fresh ≠ u → fresh ≠ m → fresh ≠ v →
    Related (u + fresh) (fresh + v) (u + m) (m + v) := by decide +kernel

private theorem vertex_lift : ∀ u m v a b : Color,
    Related a b (u + m) (m + v) →
    ∃ fresh, fresh ≠ u ∧ fresh ≠ m ∧ fresh ≠ v ∧
      a = u + fresh ∧ b = fresh + v := by decide +kernel

private theorem trace_path (u m v : Color) (tail : List Color) :
    trace (u :: m :: v :: tail) =
      (u + m) :: (m + v) :: pairmap (· + ·) v (tail ++ [u]) := by
  simp only [trace_cons, List.cons_append, pairmap_cons]

/-- Elimination preserves the complete joint trace relation and real witnesses. -/
theorem trace_exact (G : SimpleGraph V) (u m v : V) (tail : List V)
    (um : G.Adj u m) (mv : G.Adj m v) (et : List Color) :
    GraphTrace (grow G u m v) (newPorts u v tail) et ↔
      Fan (GraphTrace G (oldPorts u m v tail)) et := by
  constructor
  · rintro ⟨k, rfl⟩
    let rest := pairmap (· + ·) (k (some v)) ((tail.map fun x => k (some x)) ++ [k (some u)])
    refine ⟨k (some u) + k none, k none + k (some v),
      k (some u) + k (some m), k (some m) + k (some v), rest, ?_, ?_, restrict k, ?_⟩
    · simp only [newPorts, List.map_cons, List.map_map, trace_path]
      rfl
    · exact vertex_relation _ _ _ _ (k.valid um) (k.valid mv)
        (k.valid (show (grow G u m v).Adj none (some u) from Or.inl rfl))
        (k.valid (show (grow G u m v).Adj none (some m) from Or.inr (Or.inl rfl)))
        (k.valid (show (grow G u m v).Adj none (some v) from Or.inr (Or.inr rfl)))
    · simp only [oldPorts, List.map_cons, trace_path]
      rfl
  · rintro ⟨a, b, c, d, rest, rfl, rel, k, hk⟩
    have data : c = k u + k m ∧ d = k m + k v ∧
        rest = pairmap (· + ·) (k v) ((tail.map k) ++ [k u]) := by
      simpa only [oldPorts, List.map_cons, trace_path, List.cons.injEq] using hk
    obtain ⟨rfl, rfl, rfl⟩ := data
    obtain ⟨fresh, hu, hm, hv, rfl, rfl⟩ := vertex_lift _ _ _ _ _ rel
    refine ⟨extend k fresh hu hm hv, ?_⟩
    simp only [newPorts, List.map_cons, List.map_map, trace_path]
    rfl

/-- One successful parent strategy transports through the actual graph operation. -/
theorem repair (G : SimpleGraph V) (u m v : V) (tail : List V)
    (um : G.Adj u m) (mv : G.Adj m v)
    {a b c d : Color} (t : List Color) (rel : Related a b c d)
    (parent : KempeCoclosure (GraphTrace G (oldPorts u m v tail)) (c :: d :: t)) :
    KempeCoclosure (GraphTrace (grow G u m v) (newPorts u v tail)) (a :: b :: t) :=
  KempeBoundaryFan.repair
    (fun a b c d t h hp => (trace_exact G u m v tail um mv _).mpr
      ⟨a,b,c,d,t,rfl,h,hp⟩) t rel parent

end FourColor.BoundaryFanRepair
