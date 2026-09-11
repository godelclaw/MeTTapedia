import Mettapedia.GraphTheory.FourColor.NestedSideWireComposition

/-!
# Actual single-vertex Count transfers

Adjoining a fresh vertex to an arbitrary ambient side gives a vertex star
and persistent identity wires. Its matrix entries are zero or one, with
an explicit boundary test. The construction uses the original edge mates;
it assumes neither a supplied slab nor a connected or bounded-width sweep.
The consumer is the physical-letter stage of compositional Count closure.
No uniform frontier bound or admissible smaller replacement is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.VertexTransfer

open GoertzelV24RotationCutDartDecomposition NestedSideWire

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem.{u, u, u} V E} {inner : V → Prop} {v : V}

noncomputable section

local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def enlarged (inner : V → Prop) (v : V) : V → Prop := fun w => inner w ∨ w = v

omit [Fintype V] [DecidableEq V] in
theorem inclusion : ∀ w, inner w → enlarged inner v w := fun _ h => Or.inl h

abbrev NewDart (RS : RotationSystem.{u, u, u} V E) (inner : V → Prop) (v : V) :=
  RetainedDart RS (layer inner (enlarged inner v))

theorem newDart_base (d : NewDart RS inner v) : RS.vertOf d.1 = v :=
  d.2.1.resolve_left d.2.2

/-- The opposite dart on the old side of a newly internalized edge. -/
def incoming (d : NewDart RS inner v) (hi : inner (RS.vertOf (RS.alpha d.1))) :
    BoundaryDart RS inner :=
  ⟨⟨RS.alpha d.1, hi⟩, by simpa only [RS.alpha_involutive] using d.2.2⟩

/-- A new outgoing port. Looplessness ensures its mate is not the new vertex. -/
def outgoing (d : NewDart RS inner v) (hi : ¬ inner (RS.vertOf (RS.alpha d.1))) :
    BoundaryDart RS (enlarged inner v) :=
  ⟨⟨d.1, d.2.1⟩, fun h => h.elim hi
    (fun heq => RS.no_self_loops d.1 ((newDart_base d).trans heq.symm))⟩

/-- The colour of every new dart is forced by exactly one boundary word. -/
def forced (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS (enlarged inner v) → Color) (d : NewDart RS inner v) : Color := by
  classical
  exact if hi : inner (RS.vertOf (RS.alpha d.1)) then x (incoming d hi)
    else y (outgoing d hi)

def Accepts (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS (enlarged inner v) → Color) : Prop :=
  (∀ b, x b ≠ 0) ∧ (∀ b, y b ≠ 0) ∧ Function.Injective (forced x y) ∧
    ∀ (b : BoundaryDart RS (enlarged inner v)) (hi : inner (RS.vertOf b.1.1)),
      x (throughFromOuter inclusion b hi) = y b

theorem color_eq_forced {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS (enlarged inner v) → Color}
    {cs : SideColoring RS (layer inner (enlarged inner v))}
    (hc : LayerBoundary inclusion x y cs) (d : NewDart RS inner v) :
    cs.color d = forced x y d := by
  classical
  unfold forced
  split_ifs with hi
  · have ho : enlarged inner v (RS.vertOf (RS.alpha (incoming d hi).1.1)) := by
      simpa only [incoming, RS.alpha_involutive] using d.2.1
    have he : (⟨RS.alpha (incoming d hi).1.1, ⟨ho, (incoming d hi).2⟩⟩ :
        NewDart RS inner v) = d := Subtype.ext (RS.alpha_involutive d.1)
    simpa only [he] using hc.1 (incoming d hi) ho
  · exact hc.2.1 (outgoing d hi) d.2.2

theorem accepts_of_boundary {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS (enlarged inner v) → Color}
    {cs : SideColoring RS (layer inner (enlarged inner v))}
    (hc : LayerBoundary inclusion x y cs) : Accepts x y := by
  refine ⟨hc.input_ne_zero inclusion, hc.output_ne_zero inclusion, ?_, ?_⟩
  · intro d e heq
    by_contra hne
    exact cs.proper d e ((newDart_base d).trans (newDart_base e).symm) hne
      ((color_eq_forced hc d).trans (heq.trans (color_eq_forced hc e).symm))
  · intro b hi
    exact (hc.2.2 b hi).1

/-- Construct the actual layer colouring from the local boundary test. -/
def ofAccepts {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS (enlarged inner v) → Color} (h : Accepts x y) :
    SideColoring RS (layer inner (enlarged inner v)) where
  color := forced x y
  alpha_internal d hd := by
    exact (RS.no_self_loops d.1
      ((newDart_base d).trans (newDart_base ⟨RS.alpha d.1, hd⟩).symm)).elim
  ne_zero d := by
    classical
    unfold forced
    split_ifs
    · exact h.1 _
    · exact h.2.1 _
  proper d e _ hne := fun heq => hne (h.2.2.1 heq)

theorem boundary_ofAccepts {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS (enlarged inner v) → Color} (h : Accepts x y) :
    LayerBoundary inclusion x y (ofAccepts h) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro b ho
    change forced x y ⟨RS.alpha b.1.1, ⟨ho, b.2⟩⟩ = x b
    simp only [forced, incoming, RS.alpha_involutive, dif_pos b.1.2]
    congr 1
  · intro b hi
    change forced x y ⟨b.1.1, ⟨b.1.2, hi⟩⟩ = y b
    have hm : ¬ inner (RS.vertOf (RS.alpha b.1.1)) := fun hb => b.2 (Or.inl hb)
    simp only [forced, dif_neg hm, outgoing]
    congr 1
  · intro b hi
    exact ⟨h.2.2.2 b hi, h.1 _⟩

/-- Exact literal semantics; existence is constructed, not assumed. -/
theorem slabRel_iff (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS (enlarged inner v) → Color) :
    SlabRel inclusion x y ↔ Accepts x y :=
  ⟨fun ⟨_, hc⟩ => accepts_of_boundary hc, fun h => ⟨ofAccepts h, boundary_ofAccepts h⟩⟩

/-- Fixed boundary words determine all new dart colours, including when
all three incident edges are inputs or all are outputs. -/
theorem boundary_unique {x : BoundaryDart RS inner → Color}
    {y : BoundaryDart RS (enlarged inner v) → Color}
    {a b : SideColoring RS (layer inner (enlarged inner v))}
    (ha : LayerBoundary inclusion x y a) (hb : LayerBoundary inclusion x y b) : a = b := by
  apply coloring_ext
  funext d
  exact (color_eq_forced ha d).trans (color_eq_forced hb d).symm

theorem slabCount_eq (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS (enlarged inner v) → Color) :
    slabCount inclusion x y = if Accepts x y then 1 else 0 := by
  classical
  split_ifs with h
  · apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨ofAccepts h, boundary_ofAccepts h⟩, ?_⟩
    intro c
    exact Subtype.ext (boundary_unique c.2 (boundary_ofAccepts h))
  · apply Classical.byContradiction
    intro hn
    exact h ((slabRel_iff x y).mp ((slabCount_ne_zero_iff inclusion x y).mp hn))

/-- The actual side Count update uses the explicit zero-one vertex letter. -/
theorem sideCount_step (y : BoundaryDart RS (enlarged inner v) → Color) :
    sideCount y = ∑ x : BoundaryDart RS inner → Color,
      if Accepts x y then sideCount x else 0 := by
  classical
  rw [sideCount_eq_sum inclusion]
  apply Finset.sum_congr rfl
  intro x _
  rw [slabCount_eq]
  split_ifs <;> simp

/-- Cubicity supplies the three dart positions; this is not a supplied
realization hypothesis. -/
def starEquiv (hc : RS.IsCubic) (hv : ¬ inner v) : Fin 3 ≃ NewDart RS inner v := by
  classical
  let e : NewDart RS inner v ≃ {d : RS.D // RS.vertOf d = v} :=
    { toFun := fun d => ⟨d.1, newDart_base d⟩
      invFun := fun d => ⟨d.1, ⟨Or.inr d.2, fun h => hv (d.2 ▸ h)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card {d : RS.D // RS.vertOf d = v} = 3 := by
    simpa only [Fintype.card_subtype, RotationSystem.dartsAt] using hc v
  exact (Fintype.equivFinOfCardEq hcard).symm.trans e.symm

/-- An elementary code records the three incident ports and, separately,
the original input coordinate of every persistent output wire. -/
abbrev Code (l r : ℕ) := (Fin 3 → Fin l ⊕ Fin r) × (Fin r → Option (Fin l))

/-- A raw syntax bound, not a claim that every raw code is a planar letter. -/
theorem card_code (l r : ℕ) : Fintype.card (Code l r) = (l + r) ^ 3 * (l + 1) ^ r := by
  simp [Code]

def port (d : NewDart RS inner v) :
    BoundaryDart RS inner ⊕ BoundaryDart RS (enlarged inner v) := by
  classical
  exact if hi : inner (RS.vertOf (RS.alpha d.1)) then Sum.inl (incoming d hi)
    else Sum.inr (outgoing d hi)

theorem forced_eq (x : BoundaryDart RS inner → Color)
    (y : BoundaryDart RS (enlarged inner v) → Color) (d : NewDart RS inner v) :
    forced x y d = Sum.elim x y (port d) := by
  classical
  unfold forced port
  split_ifs <;> rfl

theorem port_injective : Function.Injective (port (RS := RS) (inner := inner) (v := v)) := by
  classical
  intro d e h
  unfold port at h
  split_ifs at h with hd he he
  · apply Subtype.ext
    apply RS.alpha.injective
    exact congrArg (fun b : BoundaryDart RS inner => b.1.1) (Sum.inl.inj h)
  · exact Subtype.ext (congrArg (fun b : BoundaryDart RS (enlarged inner v) => b.1.1)
      (Sum.inr.inj h))

variable {l r : ℕ}

def encode (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) : Code l r :=
  (fun i => Sum.map mi.symm mo.symm (port (starEquiv hc hv i)),
   fun j => if hi : inner (RS.vertOf (mo j).1.1)
     then some (mi.symm (throughFromOuter inclusion (mo j) hi)) else none)

theorem encode_star_injective (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) :
    Function.Injective (encode hc hv mi mo).1 := by
  intro i j h
  exact (starEquiv hc hv).injective (port_injective
    ((Equiv.sumCongr mi.symm mo.symm).injective h))

/-- Distinct persistent output ports cannot copy the same input edge. -/
theorem encode_wire_injective (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v)) (j k : Fin r) (i : Fin l)
    (hj : (encode hc hv mi mo).2 j = some i)
    (hk : (encode hc hv mi mo).2 k = some i) : j = k := by
  classical
  simp only [encode] at hj hk
  split_ifs at hj with hjin
  split_ifs at hk with hkin
  have he := mi.symm.injective ((Option.some.inj hj).trans (Option.some.inj hk).symm)
  apply mo.injective
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun b : BoundaryDart RS inner => b.1.1) he

/-- The finite test uses only the code, not the original graph. -/
def CodeAccepts (a : Code l r) (x : Fin l → Color) (y : Fin r → Color) : Prop :=
  (∀ i, x i ≠ 0) ∧ (∀ j, y j ≠ 0) ∧
  Function.Injective (fun t => Sum.elim x y (a.1 t)) ∧
  ∀ j i, a.2 j = some i → x i = y j

theorem encode_forced (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) (t : Fin 3) :
    Sum.elim x y ((encode hc hv mi mo).1 t) =
      forced (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) (starEquiv hc hv t) := by
  rw [forced_eq]
  change Sum.elim x y (Sum.map mi.symm mo.symm _) = _
  cases port (starEquiv hc hv t) <;> rfl

/-- The extracted letter's finite test is equivalent in both directions
to the actual boundary equations. -/
theorem codeAccepts_iff (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) :
    CodeAccepts (encode hc hv mi mo) x y ↔
      Accepts (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) := by
  classical
  constructor
  · rintro ⟨hx, hy, hs, hw⟩
    refine ⟨fun b => hx _, fun b => hy _, ?_, ?_⟩
    · intro d e heq
      have h := hs (a₁ := (starEquiv hc hv).symm d) (a₂ := (starEquiv hc hv).symm e)
      simp only [encode_forced, Equiv.apply_symm_apply] at h
      exact (starEquiv hc hv).symm.injective (h heq)
    · intro b hi
      have h := hw (mo.symm b) (mi.symm (throughFromOuter inclusion b hi))
      simp only [encode, Equiv.apply_symm_apply, dif_pos hi, forall_const] at h
      exact h
  · rintro ⟨hx, hy, hs, hw⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      simpa only [Equiv.symm_apply_apply] using hx (mi i)
    · intro j
      simpa only [Equiv.symm_apply_apply] using hy (mo j)
    · intro s t heq
      change Sum.elim x y ((encode hc hv mi mo).1 s) =
        Sum.elim x y ((encode hc hv mi mo).1 t) at heq
      rw [encode_forced, encode_forced] at heq
      exact (starEquiv hc hv).injective (hs heq)
    · intro j i heq
      change (if hi : inner (RS.vertOf (mo j).1.1) then
        some (mi.symm (throughFromOuter inclusion (mo j) hi)) else none) = some i at heq
      split_ifs at heq with hi
      · cases Option.some.inj heq
        simpa only [Equiv.symm_apply_apply] using hw (mo j) hi

/-- Exact physical Count is computed by a finite letter extracted from
the cubic rotation data. Port coordinates are explicit, not conflated. -/
theorem count_encode (hc : RS.IsCubic) (hv : ¬ inner v)
    (mi : Fin l ≃ BoundaryDart RS inner)
    (mo : Fin r ≃ BoundaryDart RS (enlarged inner v))
    (x : Fin l → Color) (y : Fin r → Color) :
    slabCount inclusion (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) =
      if CodeAccepts (encode hc hv mi mo) x y then 1 else 0 := by
  rw [slabCount_eq, codeAccepts_iff]

section Sweep

/-- The visited side of a vertex list. Evaluation processes the tail first. -/
def visited : List V → V → Prop
  | [] => fun _ => False
  | v :: rest => enlarged (visited rest) v

/-- Exact dynamic Count with the empty-side initial value one. Boundary
types change at each step and are never silently identified. -/
def sweepCount : (order : List V) → (BoundaryDart RS (visited order) → Color) → ℕ
  | [], _ => 1
  | v :: rest, y => ∑ x : BoundaryDart RS (visited rest) → Color,
      if Accepts (v := v) x y then sweepCount rest x else 0

/-- Each fresh cubic sweep step can be evaluated in finite coordinates
using only its extracted code. This is the code's actual sweep consumer. -/
theorem sweepCount_cons_code (hc : RS.IsCubic) (rest : List V)
    (hv : ¬ visited rest v) (mi : Fin l ≃ BoundaryDart RS (visited rest))
    (mo : Fin r ≃ BoundaryDart RS (enlarged (visited rest) v)) (y : Fin r → Color) :
    sweepCount (v :: rest) (fun b => y (mo.symm b)) =
      ∑ x : Fin l → Color, if CodeAccepts (encode hc hv mi mo) x y
        then sweepCount rest (fun b => x (mi.symm b)) else 0 := by
  classical
  change (∑ x : BoundaryDart RS (visited rest) → Color,
    if Accepts x (fun b => y (mo.symm b)) then sweepCount rest x else 0) = _
  symm
  apply Finset.sum_equiv (Equiv.arrowCongr mi (Equiv.refl Color))
  · intro x; simp
  · intro x _
    change (if CodeAccepts (encode hc hv mi mo) x y then _ else 0) =
      if Accepts (fun b => x (mi.symm b)) (fun b => y (mo.symm b)) then _ else 0
    rw [codeAccepts_iff]
    rfl

theorem sweepCount_eq (order : List V) (w : BoundaryDart RS (visited order) → Color) :
    sweepCount order w = sideCount w := by
  induction order with
  | nil =>
    symm
    apply Nat.card_eq_one_iff_exists.mpr
    let c : SideColoring RS (visited ([] : List V)) :=
      { color := fun d => False.elim d.2
        alpha_internal := fun d _ => False.elim d.2
        ne_zero := fun d => False.elim d.2
        proper := fun d _ _ _ => False.elim d.2 }
    refine ⟨⟨c, funext (fun b => False.elim b.1.2)⟩, ?_⟩
    intro other
    apply Subtype.ext
    apply coloring_ext
    funext d
    exact d.2.elim
  | cons v rest ih =>
    dsimp only [visited] at w
    change (∑ x : BoundaryDart RS (visited rest) → Color,
      if Accepts (v := v) x w then sweepCount rest x else 0) = sideCount w
    rw [sideCount_step]
    apply Finset.sum_congr rfl
    intro x _
    rw [ih x]

/-- Zero testing of the compiled sweep is exactly side-support testing. -/
theorem sweepCount_ne_zero_iff (order : List V)
    (w : BoundaryDart RS (visited order) → Color) :
    sweepCount order w ≠ 0 ↔ w ∈ sideSupport RS (visited order) := by
  rw [sweepCount_eq, sideCount_ne_zero_iff]

/-- Once every vertex has been processed there are no boundary ports;
the terminal fibre contains precisely all proper colourings of the map. -/
def terminalEquiv (order : List V) (hcover : ∀ v, visited order v)
    (w : BoundaryDart RS (visited order) → Color) :
    WordColoring w ≃ SideColoring RS (fun _ => True) where
  toFun c := restrict (fun v _ => hcover v) c.1
  invFun c := ⟨restrict (fun _ _ => True.intro) c, funext (fun b =>
    (b.2 (hcover _)).elim)⟩
  left_inv c := by
    apply Subtype.ext
    apply coloring_ext
    funext d
    rfl
  right_inv c := by
    apply coloring_ext
    funext d
    rfl

/-- Whole-graph Count, for any covering vertex order, without a geometric
or bounded-width premise. The sum may be large; no finite-image claim for
the natural-number Count vectors is inferred. -/
theorem sweepCount_closed (order : List V) (hcover : ∀ v, visited order v)
    (w : BoundaryDart RS (visited order) → Color) :
    sweepCount order w = Nat.card (SideColoring RS (fun _ => True)) := by
  rw [sweepCount_eq, sideCount]
  exact Nat.card_congr (terminalEquiv order hcover w)

omit [Fintype V] [DecidableEq V] in
theorem visited_iff_mem (order : List V) (v : V) : visited order v ↔ v ∈ order := by
  induction order with
  | nil => simp [visited]
  | cons w rest ih => simp only [visited, enlarged, ih, List.mem_cons, or_comm]

def completeOrder : List V := Finset.univ.toList

omit [DecidableEq V] in
theorem visited_complete (v : V) : visited (completeOrder (V := V)) v := by
  simp [visited_iff_mem, completeOrder]

def emptyTerminal : BoundaryDart RS (visited (completeOrder (V := V))) → Color :=
  fun b => (b.2 (visited_complete _)).elim

/-- A complete sweep is supplied by finite vertex enumeration, rather
than being a new hypothesis of the Count calculation. -/
theorem canonicalCount_eq :
    sweepCount (completeOrder (V := V)) (emptyTerminal (RS := RS)) =
      Nat.card (SideColoring RS (fun _ => True)) :=
  sweepCount_closed completeOrder visited_complete emptyTerminal

end Sweep

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.VertexTransfer
