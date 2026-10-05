import MettapediaFourColor.KempeFourFan
import MettapediaFourColor.BoundaryFanRepair

/-!
# Actual graph colourings after a four-neighbour boundary insertion

A new vertex is adjacent to four consecutive old boundary vertices. Its
three triangles replace three old boundary edges by two. The complete
joint trace relation remains Kempe closed. A compatible colouring exists
even when the supplied four neighbours initially use all four colours.
-/

namespace FourColor.BoundaryFourFanRepair

open Color KempeBoundarySplit KempeFourFan

variable {V : Type*}

def grow (G : SimpleGraph V) (u v w z : V) : SimpleGraph (Option V) where
  Adj
    | some x, some y => G.Adj x y
    | none, some y => y = u ∨ y = v ∨ y = w ∨ y = z
    | some x, none => x = u ∨ x = v ∨ x = w ∨ x = z
    | none, none => False
  symm := ⟨by rintro (x | _) (y | _) h <;> first | exact G.adj_symm h | exact h⟩
  loopless := ⟨by
    rintro (_ | x) h
    · exact h
    · exact G.loopless.irrefl _ h⟩

def oldPorts (u v w z : V) (tail : List V) := u :: v :: w :: z :: tail
def newPorts (u z : V) (tail : List V) := some u :: none :: some z :: tail.map some

def restrict {G : SimpleGraph V} {u v w z : V} {C : Type*}
    (k : (grow G u v w z).Coloring C) : G.Coloring C :=
  .mk (fun x => k (some x)) (fun h => k.valid h)

def extend {G : SimpleGraph V} {u v w z : V} {C : Type*}
    (k : G.Coloring C) (fresh : C)
    (hu : fresh ≠ k u) (hv : fresh ≠ k v) (hw : fresh ≠ k w) (hz : fresh ≠ k z) :
    (grow G u v w z).Coloring C :=
  .mk (fun x => x.elim fresh k) (by
    rintro (_ | x) (_ | y) h
    · exact False.elim h
    · rcases h with rfl | rfl | rfl | rfl <;> assumption
    · rcases h with rfl | rfl | rfl | rfl
      · exact hu.symm
      · exact hv.symm
      · exact hw.symm
      · exact hz.symm
    · exact k.valid h)

private theorem vertex_relation : ∀ u v w z fresh : Color,
    u ≠ v → v ≠ w → w ≠ z → fresh ≠ u → fresh ≠ v → fresh ≠ w → fresh ≠ z →
    Related (u+fresh) (fresh+z) (u+v) (v+w) (w+z) := by decide +kernel

private theorem vertex_lift : ∀ u v w z a b : Color,
    Related a b (u+v) (v+w) (w+z) →
    ∃ fresh, fresh ≠ u ∧ fresh ≠ v ∧ fresh ≠ w ∧ fresh ≠ z ∧
      a = u+fresh ∧ b = fresh+z := by decide +kernel

private theorem trace_path (u v w z : Color) (tail : List Color) :
    trace (u::v::w::z::tail) =
      (u+v)::(v+w)::(w+z)::pairmap (·+·) z (tail++[u]) := by
  simp only [trace_cons,List.cons_append,pairmap_cons]

private theorem trace_short (u z : Color) (tail : List Color) :
    trace (u::z::tail) = (u+z)::pairmap (·+·) z (tail++[u]) := by
  simp only [trace_cons,List.cons_append,pairmap_cons]

/-- Every hidden old port and the inserted vertex has a common witness. -/
theorem trace_exact (G : SimpleGraph V) (u v w z : V) (tail : List V)
    (uv : G.Adj u v) (vw : G.Adj v w) (wz : G.Adj w z) (et : List Color) :
    GraphTrace (grow G u v w z) (newPorts u z tail) et ↔
      Fan (GraphTrace G (oldPorts u v w z tail)) et := by
  constructor
  · rintro ⟨k,rfl⟩
    let rest := pairmap (·+·) (k (some z)) ((tail.map fun x => k (some x))++[k (some u)])
    refine ⟨k (some u)+k none,k none+k (some z),k (some u)+k (some v),
      k (some v)+k (some w),k (some w)+k (some z),rest,?_,?_,restrict k,?_⟩
    · simp only [newPorts,List.map_cons,List.map_map,trace_cons,List.cons_append,pairmap_cons]
      rfl
    · exact vertex_relation _ _ _ _ _ (k.valid uv) (k.valid vw) (k.valid wz)
        (k.valid (show (grow G u v w z).Adj none (some u) from Or.inl rfl))
        (k.valid (show (grow G u v w z).Adj none (some v) from Or.inr (Or.inl rfl)))
        (k.valid (show (grow G u v w z).Adj none (some w) from Or.inr (Or.inr (Or.inl rfl))))
        (k.valid (show (grow G u v w z).Adj none (some z) from Or.inr (Or.inr (Or.inr rfl))))
    · simp only [oldPorts,List.map_cons,trace_path]
      rfl
  · rintro ⟨a,b,c,d,e,rest,rfl,rel,k,hk⟩
    have data : c=k u+k v ∧ d=k v+k w ∧ e=k w+k z ∧
        rest=pairmap (·+·) (k z) ((tail.map k)++[k u]) := by
      simpa only [oldPorts,List.map_cons,trace_path,List.cons.injEq] using hk
    obtain ⟨rfl,rfl,rfl,rfl⟩ := data
    obtain ⟨fresh,hu,hv,hw,hz,rfl,rfl⟩ := vertex_lift _ _ _ _ _ _ rel
    refine ⟨extend k fresh hu hv hw hz,?_⟩
    simp only [newPorts,List.map_cons,List.map_map,trace_cons,List.cons_append,pairmap_cons]
    rfl

theorem closed (G : SimpleGraph V) (u v w z : V) (tail : List V)
    (uv : G.Adj u v) (vw : G.Adj v w) (wz : G.Adj w z)
    (h : KempeClosed (GraphTrace G (oldPorts u v w z tail))) :
    KempeClosed (GraphTrace (grow G u v w z) (newPorts u z tail)) := by
  have eq : GraphTrace (grow G u v w z) (newPorts u z tail) =
      Fan (GraphTrace G (oldPorts u v w z tail)) :=
    funext fun et => propext (trace_exact G u v w z tail uv vw wz et)
  rw [eq]
  exact KempeFourFan.closed h

/-- The colouring of the entire old graph may change. All old edges and
all old interior vertices remain properly coloured. -/
theorem colourable (G : SimpleGraph V) (u v w z : V) (tail : List V)
    (h : KempeClosed (GraphTrace G (oldPorts u v w z tail))) (C : G.Coloring Color) :
    Nonempty ((grow G u v w z).Coloring Color) := by
  let es := trace ((oldPorts u v w z tail).map C)
  have size : es.length = tail.length + 4 := by simp [es,oldPorts]
  obtain ⟨word,hw⟩ : ∃ word : Fin (tail.length+4) → Color, List.ofFn word = es := by
    rw [← size]
    exact ⟨es.get,List.ofFn_get es⟩
  have initial : GraphTrace G (oldPorts u v w z tail) (List.ofFn word) :=
    hw.symm ▸ ⟨C,rfl⟩
  obtain ⟨_,gram,matched,_⟩ := h _ initial
  have nz : ∀ i, word i ≠ 0 := by
    intro i hi
    exact matchg_notMem_zero _ [] _ matched (List.mem_ofFn.mpr ⟨i,hi⟩)
  obtain ⟨d,⟨D,hd⟩,ready⟩ := KempeFourFan.prepare h word nz initial
  have h0 : d 0 = D u + D v := by
    have e := congrArg (fun l : List Color => l.headD 0) hd
    simpa [List.ofFn_succ,oldPorts,trace_path] using e
  have h1 : d 1 = D v + D w := by
    have e := congrArg (fun l : List Color => l.tail.headD 0) hd
    simpa [List.ofFn_succ,oldPorts,trace_path] using e
  have h2 : d 2 = D w + D z := by
    have e := congrArg (fun l : List Color => l.tail.tail.headD 0) hd
    simpa [List.ofFn_succ,oldPorts,trace_path] using e
  rw [h0,h1,h2] at ready
  have lift : ∀ a b c d : Color, Ready (a+b) (b+c) (c+d) →
      ∃ fresh, fresh ≠ a ∧ fresh ≠ b ∧ fresh ≠ c ∧ fresh ≠ d := by decide +kernel
  obtain ⟨fresh,hu,hv,hw,hz⟩ := lift _ _ _ _ ready
  exact ⟨extend D fresh hu hv hw hz⟩

/-- Recentring the ordered interface preserves the same colouring relation. -/
theorem rotate_closed (G : SimpleGraph V) (ports : List V) (n : ℕ)
    (h : KempeClosed (GraphTrace G ports)) : KempeClosed (GraphTrace G (ports.rotate n)) := by
  have eq : GraphTrace G (ports.rotate n) = KempeBoundaryFan.Rotate (GraphTrace G ports) n := by
    funext et
    apply propext
    constructor
    · rintro ⟨C,rfl⟩
      exact ⟨trace (ports.map C),by rw [List.map_rotate,trace_rotate],C,rfl⟩
    · rintro ⟨es,rfl,C,rfl⟩
      exact ⟨C,by rw [List.map_rotate,trace_rotate]⟩
  rw [eq]
  exact KempeBoundaryFan.closed_rotate h n

theorem three_closed (G : SimpleGraph V) (u m v : V) (tail : List V)
    (um : G.Adj u m) (mv : G.Adj m v)
    (h : KempeClosed (GraphTrace G (BoundaryFanRepair.oldPorts u m v tail))) :
    KempeClosed (GraphTrace (BoundaryFanRepair.grow G u m v)
      (BoundaryFanRepair.newPorts u v tail)) := by
  have eq : GraphTrace (BoundaryFanRepair.grow G u m v) (BoundaryFanRepair.newPorts u v tail) =
      KempeBoundaryFan.Fan (GraphTrace G (BoundaryFanRepair.oldPorts u m v tail)) :=
    funext fun et => propext (BoundaryFanRepair.trace_exact G u m v tail um mv et)
  rw [eq]
  exact KempeBoundaryFan.closed h

theorem three_colourable (G : SimpleGraph V) (u m v : V) (C : G.Coloring Color) :
    Nonempty ((BoundaryFanRepair.grow G u m v).Coloring Color) := by
  have fresh : ∀ a b c : Color, ∃ d : Color, d ≠ a ∧ d ≠ b ∧ d ≠ c := by decide +kernel
  obtain ⟨d,hu,hm,hv⟩ := fresh (C u) (C m) (C v)
  exact ⟨BoundaryFanRepair.extend C d hu hm hv⟩

end FourColor.BoundaryFourFanRepair
