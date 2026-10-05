import MettapediaFourColor.StripPartialColouring
import MettapediaFourColor.KempeChromogramMatching
import MettapediaFourColor.GraphTraceAlignment

/-!
# A uniform first repair phase for the left end of D0099

When the end triangle has no colouring, its two outer core vertices have
the same forced colour. One anchored exchange removes this conflict for
every partner. The argument uses five boundary observations and three
positions of the partner; it contains no table of whole boundary words.
The result restores this triangle, not the rest of the core.
-/

namespace FourColor.StripEndPhase

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension
open StripPartialColouring KempeBoundarySplit

def End (x y z u v : Color) : Prop :=
  ∃ a d : Color, (a ≠ z ∧ a ≠ u ∧ a ≠ v) ∧
    (d ≠ x ∧ d ≠ y ∧ d ≠ z) ∧ a ≠ d

instance (x y z u v : Color) : Decidable (End x y z u v) := by
  unfold End
  infer_instance

def Good (b : Boundary) : Prop := ∃ a c, r0 b a c

instance (b : Boundary) : Decidable (Good b) := by unfold Good; infer_instance

theorem good_iff (b : Boundary) : Good b ↔ End (b 4) (b 5) (b 6) (b 7) (b 8) := by
  constructor
  · rintro ⟨a,c,ha,hc,hac,e,he,hae,hec⟩
    exact ⟨e,c,by simpa [unary, attachments] using he,
      by simpa [unary, attachments] using hc,hec⟩
  · rintro ⟨e,c,he,hc,hec⟩
    obtain ⟨h8,hc',he'⟩ := avoid_spec (b 8) c e
    refine ⟨avoid (b 8) c e,c,?_,?_,hc',e,?_,he',hec⟩
    · simpa [unary, attachments] using h8
    · simpa [unary, attachments] using hc
    · simpa [unary, attachments] using he

theorem repeated (x y u v : Color) : End x y x u v := by
  revert x y u v
  decide +kernel

theorem blocked_distinct : ∀ x y z u v, ¬ End x y z u v →
    x ≠ y ∧ x ≠ z ∧ y ≠ z := by decide +kernel

theorem middle_release : ∀ x y z u v, ¬ End x y z u v →
    End x ((x + z) + y) z u v := by decide +kernel

def inside (j i : Fin 11) : Bool := decide (min (4 : Fin 11) j < i ∧ i ≤ max (4 : Fin 11) j)

def update (b : Boundary) (j : Fin 11) (i : Fin 11) : Color :=
  if inside j i then (b 4 + b 6) + b i else b i

/-- The partner can lie anywhere else on the boundary. -/
theorem release (b : Boundary) (bad : ¬ Good b) (j : Fin 11) (hj : j ≠ 4) :
    Good (update b j) := by
  have blocked : ¬ End (b 4) (b 5) (b 6) (b 7) (b 8) :=
    fun h => bad ((good_iff b).mpr h)
  rw [good_iff]
  by_cases before : j < 4
  · have h : ∀ i : Fin 11, 4 < i → inside j i = false := by
      intro i hi
      simp only [inside, min_eq_right (le_of_lt before), max_eq_left (le_of_lt before),
        decide_eq_false_iff_not]
      omega
    have at4 : inside j 4 = true := by
      simp [inside, min_eq_right (le_of_lt before), max_eq_left (le_of_lt before), before]
    simp only [update, at4, h 5 (by decide), h 6 (by decide), h 7 (by decide),
      h 8 (by decide), Bool.false_eq_true, ↓reduceIte]
    have cancel : (b 4 + b 6) + b 4 = b 6 := by
      rw [add_comm (b 4) (b 6), add_assoc, add_self, add_zero]
    rw [cancel]
    exact repeated _ _ _ _
  · by_cases at5 : j = 5
    · subst j
      simpa [update, inside] using middle_release (b 4) (b 5) (b 6) (b 7) (b 8) blocked
    · have bounds : 6 ≤ j := by omega
      have le4 : (4 : Fin 11) ≤ j := by omega
      have at4 : inside j 4 = false := by
        simp [inside, min_eq_left le4, max_eq_right le4]
      have at6 : inside j 6 = true := by
        simp [inside, min_eq_left le4, max_eq_right le4, bounds]
      have equal : update b j 6 = update b j 4 := by
        simp only [update, at4, at6, Bool.false_eq_true, ↓reduceIte]
        rw [add_assoc, add_self, add_zero]
      rw [equal]
      exact repeated _ _ _ _

def next (i : Fin 11) : Fin 11 := ⟨(i.val + 1) % 11, Nat.mod_lt _ (by decide)⟩
def word (b : Boundary) (i : Fin 11) : Color := b i + b (next i)

theorem trace_word (b : Boundary) : trace (List.ofFn b) = List.ofFn (word b) := by
  rw [trace_eq_zipWith]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_zipWith, List.getElem_ofFn, List.getElem_rotate]
    rfl

theorem interval_boundary : ∀ j : Fin 11, j ≠ 4 → ∀ i,
    (inside j i != inside j (next i)) = decide (i = 4 ∨ i = j) := by decide +kernel

private theorem shifted_sum (f x y : Color) (a d : Bool) :
    (if a then f + x else x) + (if d then f + y else y) =
      if a != d then f + (x + y) else x + y := by
  cases a <;> cases d <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Bool.false_bne, Bool.true_bne, Bool.not_false, Bool.not_true]
  · rw [add_left_comm]
  · rw [add_assoc]
  · rw [add_add_add_comm, add_self, zero_add]

theorem word_update (b : Boundary) (j : Fin 11) (hj : j ≠ 4) (i : Fin 11) :
    word (update b j) i = if i = 4 ∨ i = j then (b 4 + b 6) + word b i else word b i := by
  simp only [word, update, shifted_sum, interval_boundary j hj, decide_eq_true_eq]

theorem normalized_update (b : Boundary) (j : Fin 11) (hj : j ≠ 4)
    (fixed : b 4 + b 6 = c1) (nz : ∀ i, word b i ≠ 0)
    (ha : word b 4 ≠ c1) (hm : word b j ≠ c1) :
    trace (List.ofFn (update b j)) =
      List.ofFn (KempeIntervalRepair.switch (word b) 4 j) := by
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

theorem boundary_edges : ∀ i j, input0099.graph.Adj (port i) (port j) ↔
    j = next i ∨ i = next j := by decide +kernel

theorem proper_iff (b : Boundary) : ProperBoundary b ↔ ∀ i, word b i ≠ 0 := by
  constructor
  · intro hb i hz
    exact hb i (next i) ((boundary_edges _ _).mpr (Or.inl rfl))
      (Color.add_eq_zero_iff.mp hz)
  · intro hb i j he
    rcases (boundary_edges i j).mp he with rfl | rfl
    · exact fun h => hb i (Color.add_eq_zero_iff.mpr h)
    · exact fun h => hb j (Color.add_eq_zero_iff.mpr h.symm)

def omitted : Finset (Fin 8) := {2,4,5,6,7}
abbrev EndGraph := input0099.graph.induce {v | Live omitted v}
def endPort (i : Fin 11) : {v : Fin 19 // Live omitted v} := ⟨port i, live_port omitted i⟩
abbrev Terminal := GraphTrace EndGraph (List.ofFn endPort)

/-- The joint triangle choices colour the actual induced source, including
every retained attachment and the whole ordered boundary. -/
theorem reconstruct (b : Boundary) (hb : ProperBoundary b) (hg : Good b) :
    Terminal (trace (List.ofFn b)) := by
  obtain ⟨a,c,ha,hc,hac,e,he,hae,hec⟩ := hg
  let f : Fin 8 → Color := ![e,a,c0,c,c0,c0,c0,c0]
  have valid : ValidExcept b omitted f := by
    constructor
    · intro v hv
      fin_cases v <;> simp_all [omitted, f]
    · intro edge hm
      simp only [edges, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [omitted, f, ne_comm]
  let k : EndGraph.Coloring Color := .mk (fun v => completeColour b f v.val)
    (fun {u v} edge => partial_valid b omitted f hb valid u.val v.val
      u.property v.property edge)
  refine ⟨k, ?_⟩
  simp only [List.map_ofFn, Function.comp_def]
  rfl

/-- Every proper input reaches a compatible colouring of the left triangle.
One anchor works for every matching supplied by the same exterior. -/
theorem repair (b : Boundary) (hb : ProperBoundary b) :
    KempeCoclosure Terminal (trace (List.ofFn b)) := by
  intro outside closed initial
  by_cases ready : Good b
  · exact ⟨_,reconstruct b hb ready,initial⟩
  have bd := blocked_distinct (b 4) (b 5) (b 6) (b 7) (b 8)
    (fun h => ready ((good_iff b).mpr h))
  have nonzero : b 4 + b 6 ≠ 0 := fun h => bd.2.1 (Color.add_eq_zero_iff.mp h)
  let g := EdgePerm.rotTo (b 4 + b 6)
  let d : Boundary := fun i => g (b i)
  have proper : ProperBoundary d := fun i j he h => hb i j he (EdgePerm.apply_injective g h)
  have fixed : d 4 + d 6 = c1 := by
    change g (b 4) + g (b 6) = c1
    rw [← EdgePerm.apply_add]
    exact EdgePerm.rotTo_apply_self nonzero
  have mapped : trace (List.ofFn d) = (trace (List.ofFn b)).map g := by
    rw [← trace_map]
    simp only [List.map_ofFn, Function.comp_def, d]
  have retained : outside (trace (List.ofFn d)) := mapped ▸ (closed _ initial).1 g
  by_cases good : Good d
  · exact ⟨_,reconstruct d proper good,retained⟩
  have distinct := blocked_distinct (d 4) (d 5) (d 6) (d 7) (d 8)
    (fun h => good ((good_iff d).mpr h))
  have active : word d 4 ≠ c1 := by
    intro h
    have equal : d 4 + d 5 = d 4 + d 6 := by simpa [word, next] using h.trans fixed.symm
    exact distinct.2.2 (add_left_cancel equal)
  obtain ⟨_,w,matched,stable⟩ := closed _ retained
  rw [trace_word] at matched
  obtain ⟨m,inv,_,fixed_mate,exchange⟩ := KempeChromogramMatching.recover (word d) w matched
  have different : m 4 ≠ 4 := fun h => active ((fixed_mate 4).mp h)
  have partner : word d (m 4) ≠ c1 := by
    intro h
    have eq := (fixed_mate (m 4)).mpr h
    rw [inv] at eq
    exact different eq.symm
  have changed : matchg [] (trace (List.ofFn (update d (m 4)))) w := by
    rw [normalized_update d (m 4) different fixed ((proper_iff d).mp proper) active partner]
    exact exchange 4 active
  have new_proper : ProperBoundary (update d (m 4)) := by
    apply (proper_iff _).mpr
    intro i zero
    have nz := matchg_notMem_zero _ [] w changed
    rw [trace_word] at nz
    apply nz
    exact List.mem_ofFn.mpr ⟨i,zero⟩
  exact ⟨_,reconstruct _ new_proper (release d good (m 4) different),stable _ changed⟩

/-- The partial source and a genuine recoloured exterior agree at all ports,
including repeated ports. Five core vertices remain to be restored. -/
theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports))) (b : Boundary)
    (hb : ProperBoundary b) (initial : GraphTrace H (List.ofFn ports) (trace (List.ofFn b))) :
    ∃ D : H.Coloring Color, ∃ k : EndGraph.Coloring Color,
      ∀ i, k (endPort i) = D (ports i) := by
  obtain ⟨_,⟨k,hk⟩,⟨D,hD⟩⟩ := repair b hb _ closed initial
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align (List.ofFn endPort) k
    ((List.ofFn ports).map D) (by simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (endPort i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [List.map_ofFn, Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

end FourColor.StripEndPhase
