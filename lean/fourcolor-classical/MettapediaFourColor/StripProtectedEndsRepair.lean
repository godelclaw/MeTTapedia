import MettapediaFourColor.StripProtectedEnds

/-!
# Compatible six-vertex restoration with a protected palette

The two end triangles use disjoint core vertices. Their witnesses combine
into the induced source with only vertices 2 and 4 omitted. The right-end
exchange retains the same exterior predicate while the safe palette keeps
the left end colourable. Existing interior colours may change.
-/

namespace FourColor.StripProtectedEnds

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension
open StripPartialColouring KempeBoundarySplit
open StripEndPhase (word next trace_word proper_iff)

def omitted : Finset (Fin 8) := {2,4}
abbrev EndsGraph := input0099.graph.induce {v | Live omitted v}
def endPort (i : Fin 11) : {v : Fin 19 // Live omitted v} := ⟨port i,live_port omitted i⟩
abbrev Terminal := GraphTrace EndsGraph (List.ofFn endPort)

/-- Both end witnesses reconstruct all six retained vertices and every
retained attachment, fixing the same ordered eleven-port boundary. -/
theorem reconstruct (b : Boundary) (hb : ProperBoundary b)
    (hl : StripEndPhase.Good b) (hr : RightOK b) : Terminal (trace (List.ofFn b)) := by
  rcases hl with ⟨a1,a3,h1,h3,h13,a0,h0,h10,h03⟩
  rcases hr with ⟨a5,a6,h5,h6,h56,a7,h7,h57,h76⟩
  let f : Fin 8 → Color := ![a0,a1,c0,a3,c0,a5,a6,a7]
  have valid : ValidExcept b omitted f := by
    constructor
    · intro v hv
      fin_cases v <;> simp_all [omitted,f]
    · intro edge hm
      simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [omitted,f,ne_comm]
  let k : EndsGraph.Coloring Color := .mk (fun v => completeColour b f v.val)
    (fun {u v} he => partial_valid b omitted f hb valid u.val v.val u.property v.property he)
  refine ⟨k,?_⟩
  simp only [List.map_ofFn,Function.comp_def]
  rfl

private theorem shifted_sum (f x y : Color) (a d : Bool) :
    (if a then f + x else x) + (if d then f + y else y) =
      if a != d then f + (x + y) else x + y := by
  cases a <;> cases d <;> simp only [Bool.false_eq_true,↓reduceIte,
    Bool.false_bne,Bool.true_bne,Bool.not_false,Bool.not_true]
  · rw [add_left_comm]
  · rw [add_assoc]
  · rw [add_add_add_comm,add_self,zero_add]

theorem word_update (b : Boundary) (f : Color) (j : Fin 11) (hj : j ≠ 9) (i : Fin 11) :
    word (update b f j) i = if i = 9 ∨ i = j then f + word b i else word b i := by
  simp only [word,update,shifted_sum,StripDiamondPhase.interval_boundary 9 j hj,
    decide_eq_true_eq]

theorem normalized_update (b : Boundary) (j : Fin 11) (hj : j ≠ 9)
    (nz : ∀ i, word b i ≠ 0) (ha : word b 9 ≠ c1) (hm : word b j ≠ c1) :
    trace (List.ofFn (update b c1 j)) =
      List.ofFn (KempeIntervalRepair.switch (word b) 9 j) := by
  rw [trace_word]
  apply congrArg List.ofFn
  funext i
  rw [word_update b c1 j hj]
  simp only [KempeIntervalRepair.switch]
  split
  · rename_i h
    have hi : word b i ≠ c1 := by rcases h with rfl | rfl <;> assumption
    have algebra : ∀ c : Color, c ≠ 0 → c ≠ c1 → c1 + c = EdgePerm.e132 c := by decide +kernel
    exact algebra _ (nz i) hi
  · rfl

/-- A permitted safe palette restores both ends against every matching
supplied by the original exterior. Only the two bridge vertices remain. -/
theorem repair (b : Boundary) (hb : ProperBoundary b) (f : Color)
    (family : Family b f) (safe : Safe f (left b)) :
    KempeCoclosure Terminal (trace (List.ofFn b)) := by
  intro outside closed initial
  have hp := family.2.2.2
  have nonzero := hp.2.2.1
  let g := EdgePerm.rotTo f
  let d : Boundary := fun i => g (b i)
  have proper : ProperBoundary d := fun i j he h => hb i j he (EdgePerm.apply_injective g h)
  have fixed : g f = c1 := EdgePerm.rotTo_apply_self nonzero
  have family' : Family d c1 := by simpa only [fixed] using family_map b f g family
  have safe' : Safe c1 (left d) := by simpa only [fixed] using safe_map b f g safe
  have mapped : trace (List.ofFn d) = (trace (List.ofFn b)).map g := by
    rw [← trace_map]
    simp only [List.map_ofFn,Function.comp_def,d]
  have retained : outside (trace (List.ofFn d)) := mapped ▸ (closed _ initial).1 g
  have ha : word d 9 ≠ c1 := by
    have hp := family'.2.2.2
    simpa [word,next] using hp.2.2.2.1.symm
  obtain ⟨_,w,matched,stable⟩ := closed _ retained
  rw [trace_word] at matched
  obtain ⟨m,inv,_,fixed_mate,exchange⟩ := KempeChromogramMatching.recover (word d) w matched
  have different : m 9 ≠ 9 := fun h => ha ((fixed_mate 9).mp h)
  have partner : word d (m 9) ≠ c1 := by
    intro h
    have eq := (fixed_mate (m 9)).mpr h
    rw [inv] at eq
    exact different eq.symm
  have changed : matchg [] (trace (List.ofFn (update d c1 (m 9)))) w := by
    rw [normalized_update d (m 9) different ((proper_iff d).mp proper) ha partner]
    exact exchange 9 ha
  have new_proper : ProperBoundary (update d c1 (m 9)) := by
    apply (proper_iff _).mpr
    intro i zero
    have nz := matchg_notMem_zero _ [] w changed
    rw [trace_word] at nz
    exact nz (List.mem_ofFn.mpr ⟨i,zero⟩)
  obtain ⟨hl,hr⟩ := both_release d c1 family' safe' (m 9) different
  exact ⟨_,reconstruct _ new_proper hl hr,stable _ changed⟩

theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports))) (b : Boundary)
    (hb : ProperBoundary b) (f : Color) (family : Family b f) (safe : Safe f (left b))
    (initial : GraphTrace H (List.ofFn ports) (trace (List.ofFn b))) :
    ∃ D : H.Coloring Color, ∃ k : EndsGraph.Coloring Color,
      ∀ i, k (endPort i) = D (ports i) := by
  obtain ⟨_,⟨k,hk⟩,⟨D,hD⟩⟩ := repair b hb f family safe _ closed initial
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align (List.ofFn endPort) k
    ((List.ofFn ports).map D) (by simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (endPort i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [List.map_ofFn,Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

/-- Two boundary forms consume the same protected repair law. -/
def boundaryExample : Bool → Boundary
  | false => ![c0,c1,c0,c1,c0,c1,c0,c1,c3,c0,c1]
  | true => ![c0,c1,c0,c2,c3,c2,c3,c2,c3,c0,c1]

theorem example_guards : ∀ s, ProperBoundary (boundaryExample s) ∧
    Family (boundaryExample s) c2 ∧ Safe c2 (left (boundaryExample s)) := by
  intro s
  cases s <;> refine ⟨by decide +kernel, ?_, by decide +kernel⟩ <;>
    unfold Family <;> decide +kernel

theorem example_repair (s : Bool) :
    KempeCoclosure Terminal (trace (List.ofFn (boundaryExample s))) :=
  repair _ (example_guards s).1 c2 (example_guards s).2.1 (example_guards s).2.2

end FourColor.StripProtectedEnds
