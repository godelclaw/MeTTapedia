import MettapediaFourColor.StripDiamondPhase

/-! # Compatible composition of the triangle and diamond phases

Both phases retain the same exterior predicate. The second phase may change
the first triangle's colours; reconstruction supplies one joint colouring
of all four retained core vertices and the complete ordered boundary.
-/

namespace FourColor.StripDiamondPhase

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension
open StripPartialColouring KempeBoundarySplit
open StripEndPhase (word next trace_word proper_iff)

theorem interval_boundary : ∀ a j : Fin 11, j ≠ a → ∀ i,
    (inside a j i != inside a j (next i)) = decide (i = a ∨ i = j) := by decide +kernel

private theorem shifted_sum (f x y : Color) (a d : Bool) :
    (if a then f + x else x) + (if d then f + y else y) =
      if a != d then f + (x + y) else x + y := by
  cases a <;> cases d <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true]
  · rw [add_left_comm]
  · rw [add_assoc]
  · rw [add_add_add_comm, add_self, zero_add]

theorem word_update (b : Boundary) (j : Fin 11) (hj : j ≠ anchor b) (i : Fin 11) :
    word (update b j) i = if i = anchor b ∨ i = j then difference b + word b i else word b i := by
  simp only [word, update, shifted_sum, interval_boundary (anchor b) j hj, decide_eq_true_eq]

theorem normalized_update (b : Boundary) (j : Fin 11) (hj : j ≠ anchor b)
    (fixed : difference b = c1) (nz : ∀ i, word b i ≠ 0)
    (ha : word b (anchor b) ≠ c1) (hm : word b j ≠ c1) :
    trace (List.ofFn (update b j)) =
      List.ofFn (KempeIntervalRepair.switch (word b) (anchor b) j) := by
  rw [trace_word]
  apply congrArg List.ofFn
  funext i
  rw [word_update b j hj, fixed]
  simp only [KempeIntervalRepair.switch]
  split
  · rename_i h
    have hi : word b i ≠ c1 := by rcases h with rfl | rfl <;> assumption
    have algebra : ∀ c : Color, c ≠ 0 → c ≠ c1 → c1 + c = EdgePerm.e132 c := by decide +kernel
    exact algebra _ (nz i) hi
  · rfl

def omitted : Finset (Fin 8) := {4,5,6,7}
abbrev DiamondGraph := input0099.graph.induce {v | Live omitted v}
def diamondPort (i : Fin 11) : {v : Fin 19 // Live omitted v} := ⟨port i, live_port omitted i⟩
abbrev Terminal := GraphTrace DiamondGraph (List.ofFn diamondPort)

theorem reconstruct (b : Boundary) (hb : ProperBoundary b) (hg : Good b) :
    Terminal (trace (List.ofFn b)) := by
  obtain ⟨a1,a2,h1,h2,h12,a3,h3,hr0,h32⟩ := hg
  rcases hr0 with ⟨_,_,h13,a0,h0,h10,h03⟩
  let f : Fin 8 → Color := ![a0,a1,a2,a3,c0,c0,c0,c0]
  have valid : ValidExcept b omitted f := by
    constructor
    · intro v hv
      fin_cases v <;> simp_all [omitted, f]
    · intro edge hm
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [omitted, f, ne_comm]
  let k : DiamondGraph.Coloring Color := .mk (fun v => completeColour b f v.val)
    (fun {u v} edge => partial_valid b omitted f hb valid u.val v.val
      u.property v.property edge)
  refine ⟨k, ?_⟩
  simp only [List.map_ofFn, Function.comp_def]
  rfl

private theorem unary_map (b : Boundary) (v : Fin 8) (a : Color) (g : EdgePerm)
    (h : unary b v a) : unary (fun i => g (b i)) v (g a) :=
  fun i hi eq => h i hi (EdgePerm.apply_injective g eq)

theorem left_map (b : Boundary) (g : EdgePerm) (h : StripEndPhase.Good b) :
    StripEndPhase.Good (fun i => g (b i)) := by
  rcases h with ⟨a,c,ha,hc,hac,e,he,hae,hec⟩
  exact ⟨g a,g c,unary_map _ _ _ g ha,unary_map _ _ _ g hc,
    fun eq => hac (EdgePerm.apply_injective g eq),g e,unary_map _ _ _ g he,
    fun eq => hae (EdgePerm.apply_injective g eq),fun eq => hec (EdgePerm.apply_injective g eq)⟩

theorem difference_map (b : Boundary) (g : EdgePerm) :
    difference (fun i => g (b i)) = g (difference b) := by
  have eq : g (b 8) = g (b 3) ↔ b 8 = b 3 := (EdgePerm.apply_injective g).eq_iff
  simp only [difference, eq]
  split <;> exact (EdgePerm.apply_add g _ _).symm

/-- One anchored exchange adds vertex 2, keeping the same exterior. -/
theorem second (b : Boundary) (hb : ProperBoundary b) (left : StripEndPhase.Good b) :
    KempeCoclosure Terminal (trace (List.ofFn b)) := by
  intro outside closed initial
  by_cases ready : Good b
  · exact ⟨_,reconstruct b hb ready,initial⟩
  have nz := (active b (pattern b hb left ready)).1
  let g := EdgePerm.rotTo (difference b)
  let d : Boundary := fun i => g (b i)
  have proper : ProperBoundary d := fun i j he h => hb i j he (EdgePerm.apply_injective g h)
  have left' : StripEndPhase.Good d := left_map b g left
  have fixed : difference d = c1 := by
    rw [difference_map]
    exact EdgePerm.rotTo_apply_self nz
  have mapped : trace (List.ofFn d) = (trace (List.ofFn b)).map g := by
    rw [← trace_map]
    simp only [List.map_ofFn, Function.comp_def, d]
  have retained : outside (trace (List.ofFn d)) := mapped ▸ (closed _ initial).1 g
  by_cases good : Good d
  · exact ⟨_,reconstruct d proper good,retained⟩
  have ha : word d (anchor d) ≠ c1 := by
    simpa only [fixed] using (active d (pattern d proper left' good)).2
  obtain ⟨_,w,matched,stable⟩ := closed _ retained
  rw [trace_word] at matched
  obtain ⟨m,inv,_,fixed_mate,exchange⟩ := KempeChromogramMatching.recover (word d) w matched
  have different : m (anchor d) ≠ anchor d := fun h => ha ((fixed_mate _).mp h)
  have partner : word d (m (anchor d)) ≠ c1 := by
    intro h
    have eq := (fixed_mate (m (anchor d))).mpr h
    rw [inv] at eq
    exact different eq.symm
  have changed : matchg [] (trace (List.ofFn (update d (m (anchor d))))) w := by
    rw [normalized_update d _ different fixed ((proper_iff d).mp proper) ha partner]
    exact exchange _ ha
  have new_proper : ProperBoundary (update d (m (anchor d))) := by
    apply (proper_iff _).mpr
    intro i zero
    have nz := matchg_notMem_zero _ [] w changed
    rw [trace_word] at nz
    apply nz
    exact List.mem_ofFn.mpr ⟨i,zero⟩
  exact ⟨_,reconstruct _ new_proper (release d proper left' good _ different),stable _ changed⟩

theorem left_of_source (b : Boundary) (k : StripEndPhase.EndGraph.Coloring Color)
    (hb : ∀ i, k (StripEndPhase.endPort i) = b i) : StripEndPhase.Good b := by
  obtain ⟨f,hU,hE⟩ := validExcept_of_source b StripEndPhase.omitted k hb
  refine ⟨f 1,f 3,hU 1 (by decide),hU 3 (by decide),?_,f 0,hU 0 (by decide),?_,?_⟩
  · exact hE (1,3) (by decide) (by decide) (by decide)
  · exact (hE (0,1) (by decide) (by decide) (by decide)).symm
  · exact hE (0,3) (by decide) (by decide) (by decide)

/-- The triangle theorem supplies the second phase for every proper input.
The intermediate trace remains in the original exterior predicate. -/
theorem repair (b : Boundary) (hb : ProperBoundary b) :
    KempeCoclosure Terminal (trace (List.ofFn b)) := by
  intro outside closed initial
  obtain ⟨et,⟨k,hk⟩,retained⟩ := StripEndPhase.repair b hb outside closed initial
  let d : Boundary := fun i => k (StripEndPhase.endPort i)
  have proper : ProperBoundary d := fun i j edge => k.valid edge
  have left : StripEndPhase.Good d := left_of_source d k (fun _ => rfl)
  have eq : et = trace (List.ofFn d) := by
    simpa only [List.map_ofFn, Function.comp_def, d] using hk
  exact second d proper left outside closed (eq ▸ retained)

theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports))) (b : Boundary)
    (hb : ProperBoundary b) (initial : GraphTrace H (List.ofFn ports) (trace (List.ofFn b))) :
    ∃ D : H.Coloring Color, ∃ k : DiamondGraph.Coloring Color,
      ∀ i, k (diamondPort i) = D (ports i) := by
  obtain ⟨_,⟨k,hk⟩,⟨D,hD⟩⟩ := repair b hb _ closed initial
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align (List.ofFn diamondPort) k
    ((List.ofFn ports).map D) (by simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (diamondPort i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [List.map_ofFn, Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

end FourColor.StripDiamondPhase
