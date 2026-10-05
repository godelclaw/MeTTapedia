import MettapediaFourColor.StripFanProgram

/-!
# Retaining the five triangles between two source boundaries

Two adjacent insertions retain eleven edge observations, including the
four old boundary edges and the internal edges of the five triangles.
A selection constant on each triangle's active pair preserves these joint
constraints. Its changed observations reconstruct both inserted vertices
over an actual colouring of the same exterior.
-/

namespace FourColor.CapJointTransport

open Color

abbrev Field := Fin 11 → Color

/-- Local vertices are the old path `a,b,c,d,e`, followed by `x,y`. -/
def ends : Fin 11 → Fin 7 × Fin 7 :=
  ![(0,1),(1,2),(2,3),(3,4),(0,6),(6,5),(5,4),(1,6),(2,6),(2,5),(3,5)]

def faces : Fin 5 → Fin 11 × Fin 11 × Fin 11 :=
  ![(0,4,7),(1,7,8),(8,9,5),(2,9,10),(3,10,6)]

def Good (w : Field) : Prop :=
  (∀ i, w i ≠ 0) ∧ ∀ j, w (faces j).1 + w (faces j).2.1 = w (faces j).2.2

def flip (f a : Color) (selected : Bool) : Color :=
  if selected && decide (a ≠ f) then a + f else a

def switched (f : Color) (selected : Fin 11 → Bool) (w : Field) : Field :=
  fun i => flip f (w i) (selected i)

/-- A whole component selects both active edges of every triangle it visits. -/
def Respects (f : Color) (selected : Fin 11 → Bool) (w : Field) : Prop :=
  ∀ j, let t := faces j
    (w t.1 ≠ f → w t.2.1 ≠ f → selected t.1 = selected t.2.1) ∧
    (w t.1 ≠ f → w t.2.2 ≠ f → selected t.1 = selected t.2.2) ∧
    (w t.2.1 ≠ f → w t.2.2 ≠ f → selected t.2.1 = selected t.2.2)

private theorem flip_nonzero : ∀ f a : Color, ∀ s : Bool,
    f ≠ 0 → a ≠ 0 → flip f a s ≠ 0 := by decide +kernel

/-- The same triangle calculation is used at every junction. -/
theorem triangle_switch : ∀ f a b c : Color, ∀ sa sb sc : Bool,
    f ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 → a+b=c →
    (a ≠ f → b ≠ f → sa=sb) →
    (a ≠ f → c ≠ f → sa=sc) →
    (b ≠ f → c ≠ f → sb=sc) →
    flip f a sa + flip f b sb = flip f c sc := by decide +kernel

theorem switched_good (w : Field) (good : Good w) (f : Color) (nf : f ≠ 0)
    (selected : Fin 11 → Bool) (respect : Respects f selected w) :
    Good (switched f selected w) := by
  refine ⟨fun i => flip_nonzero f (w i) (selected i) nf (good.1 i), ?_⟩
  intro j
  exact triangle_switch _ _ _ _ _ _ _ nf (good.1 _) (good.1 _) (good.1 _)
    (good.2 j) (respect j).1 (respect j).2.1 (respect j).2.2

variable {V : Type*}

def graph (G : SimpleGraph V) (a b c d e : V) : SimpleGraph (Option (Option V)) :=
  BoundaryFourFanRepair.grow (BoundaryFanRepair.grow G c d e)
    (some a) (some b) (some c) none

def point (a b c d e : V) : Fin 7 → Option (Option V) :=
  ![some (some a),some (some b),some (some c),some (some d),some (some e),some none,none]

def observe {G : SimpleGraph V} {a b c d e : V}
    (C : (graph G a b c d e).Coloring Color) : Field :=
  fun i => C (point a b c d e (ends i).1) + C (point a b c d e (ends i).2)

private theorem triangle_sum : ∀ a b c : Color, (a+b)+(a+c)=b+c := by decide +kernel

theorem observe_good {G : SimpleGraph V} {a b c d e : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d) (de : G.Adj d e)
    (C : (graph G a b c d e).Coloring Color) : Good (observe C) := by
  have adjacent : ∀ i, (graph G a b c d e).Adj
      (point a b c d e (ends i).1) (point a b c d e (ends i).2) := by
    intro i
    fin_cases i <;> simp [ends,point,graph,BoundaryFanRepair.grow,
      BoundaryFourFanRepair.grow,ab,bc,cd,de]
  constructor
  · intro i eq
    exact C.valid (adjacent i) (Color.add_eq_zero_iff.mp eq)
  · intro j
    fin_cases j <;> dsimp only [faces,observe,ends,Matrix.cons_val]
    all_goals first | exact triangle_sum _ _ _
                    | exact (triangle_sum _ _ _).trans (add_comm _ _)

private theorem chain : ∀ a b c : Color, (a+b)+(b+c)=a+c := by decide +kernel
private theorem reverse_triangle : ∀ a b c : Color, a+b=c → a+c=b := by decide +kernel

/-- Reconstruction is algebraic and retains every old vertex, not just its trace. -/
theorem reconstruct {G : SimpleGraph V} (a b c d e : V) (D : G.Coloring Color)
    (w : Field) (good : Good w)
    (old : D a + D b = w 0 ∧ D b + D c = w 1 ∧
      D c + D d = w 2 ∧ D d + D e = w 3) :
    ∃ C : (graph G a b c d e).Coloring Color,
      (∀ v, C (some (some v)) = D v) ∧ observe C = w := by
  let x := D c + w 9
  let y := D c + w 8
  have cx : D c + x = w 9 := by simp [x,← add_assoc]
  have cy : D c + y = w 8 := by simp [y,← add_assoc]
  have by' : D b + y = w 7 := by
    rw [← chain (D b) (D c) y,old.2.1,cy]
    exact reverse_triangle _ _ _ (good.2 1)
  have ay : D a + y = w 4 := by
    rw [← chain (D a) (D b) y,old.1,by']
    exact reverse_triangle _ _ _ (good.2 0)
  have dx : D d + x = w 10 := by
    rw [← chain (D d) (D c) x,add_comm (D d) (D c),old.2.2.1,cx]
    exact good.2 3
  have ex : D e + x = w 6 := by
    rw [← chain (D e) (D d) x,add_comm (D e) (D d),old.2.2.2,dx]
    exact good.2 4
  have yx : y + x = w 5 := by
    rw [← chain y (D c) x,add_comm y (D c),cy,cx]
    exact good.2 2
  have ne {u v : Color} {i : Fin 11} (eq : u+v=w i) : u ≠ v := by
    intro same
    apply good.1 i
    rw [← eq,same,Color.add_self]
  let first : (BoundaryFanRepair.grow G c d e).Coloring Color :=
    BoundaryFanRepair.extend D x (ne cx).symm (ne dx).symm (ne ex).symm
  let C : (graph G a b c d e).Coloring Color :=
    BoundaryFourFanRepair.extend (u := some a) (v := some b) (w := some c) (z := none)
      first y (ne ay).symm (ne by').symm (ne cy).symm (ne yx)
  refine ⟨C,fun _ => rfl,?_⟩
  funext i
  fin_cases i <;> change _ + _ = _
  · exact old.1
  · exact old.2.1
  · exact old.2.2.1
  · exact old.2.2.2
  · exact ay
  · exact yx
  · change x + D e = w 6
    rw [add_comm]
    exact ex
  · exact by'
  · exact cy
  · exact cx
  · exact dx

/-- Every compatible exterior answer lifts through a selected component batch. -/
theorem lift_selection {G : SimpleGraph V} (a b c d e : V)
    (w : Field) (good : Good w) (f : Color) (nf : f ≠ 0)
    (selected : Fin 11 → Bool) (respect : Respects f selected w)
    (D : G.Coloring Color)
    (old : D a + D b = switched f selected w 0 ∧
      D b + D c = switched f selected w 1 ∧
      D c + D d = switched f selected w 2 ∧
      D d + D e = switched f selected w 3) :
    ∃ C : (graph G a b c d e).Coloring Color,
      (∀ v, C (some (some v)) = D v) ∧ observe C = switched f selected w :=
  reconstruct a b c d e D _ (switched_good w good f nf selected respect) old

/-- An answer accepted by the original exterior supplies the old colouring.
The same answer and all eleven changed cap observations are reconstructed. -/
theorem lift_chromogram {G : SimpleGraph V} (a b c d e : V) (tail : List V)
    (w : Field) (good : Good w) (f : Color) (nf : f ≠ 0)
    (selected : Fin 11 → Bool) (respect : Respects f selected w)
    (gram : Chromogram)
    (exterior : ∀ es, matchg [] es gram →
      KempeBoundarySplit.GraphTrace G (a::b::c::d::e::tail) es)
    (rest : List Color)
    (answer : matchg [] (switched f selected w 0 :: switched f selected w 1 ::
      switched f selected w 2 :: switched f selected w 3 :: rest) gram) :
    ∃ D : G.Coloring Color, ∃ C : (graph G a b c d e).Coloring Color,
      trace ((a::b::c::d::e::tail).map D) =
        switched f selected w 0 :: switched f selected w 1 ::
        switched f selected w 2 :: switched f selected w 3 :: rest ∧
      (∀ v, C (some (some v)) = D v) ∧ observe C = switched f selected w := by
  obtain ⟨D,hD⟩ := exterior _ answer
  have old : D a + D b = switched f selected w 0 ∧
      D b + D c = switched f selected w 1 ∧
      D c + D d = switched f selected w 2 ∧
      D d + D e = switched f selected w 3 := by
    have eq := hD.symm
    simp only [List.map_cons,trace_cons,List.cons_append,pairmap_cons,List.cons.injEq] at eq
    exact ⟨eq.1,eq.2.1,eq.2.2.1,eq.2.2.2.1⟩
  obtain ⟨C,hC,hw⟩ := lift_selection a b c d e w good f nf selected respect D old
  exact ⟨D,C,hD.symm,hC,hw⟩

/-- The retained cap is exactly the first two D0099 insertions. -/
theorem source_consumer {H : SimpleGraph V} (p : Fin 11 → V)
    (w : Field) (good : Good w) (f : Color) (nf : f ≠ 0)
    (selected : Fin 11 → Bool) (respect : Respects f selected w)
    (D : H.Coloring Color)
    (old : D (p 4) + D (p 5) = switched f selected w 0 ∧
      D (p 5) + D (p 6) = switched f selected w 1 ∧
      D (p 6) + D (p 7) = switched f selected w 2 ∧
      D (p 7) + D (p 8) = switched f selected w 3) :
    ∃ C : (StripFanProgram.graph2 H p).Coloring Color,
      (∀ v, C (some (some v)) = D v) ∧
        observe (a := p 4) (b := p 5) (c := p 6) (d := p 7) (e := p 8) C =
          switched f selected w :=
  lift_selection (p 4) (p 5) (p 6) (p 7) (p 8) w good f nf selected respect D old

end FourColor.CapJointTransport
