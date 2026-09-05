import Mettapedia.GraphTheory.FourColor.CapExclusion
import Mettapedia.GraphTheory.FourColor.PermCycleCount
import Mettapedia.GraphTheory.FourColor.ReachClosure

/-!
# Presented caps and their disc facts, decided

A cap is presented by a list of vertex triples of slots (an interior edge end or a port)
with the positions of the two ends of each edge and of each port; validity is decidable.
From a valid presentation the open tangle is built generically (`toCap`): interior darts
are edge ends, the involution swaps the ends, the rotation cycles the three slots of a
vertex.  Cubicity and cyclic rotations then hold for every valid presentation.  The
remaining disc facts of `CapDiscData` (connectedness, boundary-essentiality, distinct hub
faces, the spherical Euler count) are decided by the verified reachability closure and
cycle counter on the concrete data (`capDiscData_of_check`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation
namespace PresentedCap

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24SeamExchange
open GoertzelV24CompositeSphericity
open PermCycleCount ReachClosure

/-- a slot of a vertex triple: an interior edge end or a port -/
inductive Slot (N k : Nat)
  | edge (e : Fin N)
  | port (i : Fin k)
  deriving DecidableEq, Repr

/-- a position: a vertex and one of its three slots -/
abbrev Pos (V : Nat) := Fin V × Fin 3

/-- a presentation: `V` vertices with triples of slots, `N` interior edges with the
positions of their two ends, `k` ports with their positions -/
structure Pres (V N k : Nat) where
  tri : Fin V → Fin 3 → Slot N k
  endPos : Fin N → Bool → Pos V
  portPos : Fin k → Pos V

namespace Pres

variable {V N k : Nat} (P : Pres V N k)

def slotAt (p : Pos V) : Slot N k := P.tri p.1 p.2

/-- validity -/
def Valid : Prop :=
  (∀ e b, P.slotAt (P.endPos e b) = Slot.edge e) ∧
  (∀ e, (P.endPos e false).1 ≠ (P.endPos e true).1) ∧
  (∀ i, P.slotAt (P.portPos i) = Slot.port i) ∧
  (∀ p : Pos V,
    (∀ e, P.slotAt p = Slot.edge e → p = P.endPos e false ∨ p = P.endPos e true) ∧
    (∀ i, P.slotAt p = Slot.port i → p = P.portPos i))

instance decValid : Decidable P.Valid := by
  unfold Valid
  infer_instance

/-- interior darts: edge ends -/
abbrev IDart := Fin N × Bool

/-- all darts -/
abbrev D := IDart (N := N) ⊕ Fin k

/-- the position of a dart -/
def pos : D (N := N) (k := k) → Pos V
  | Sum.inl (e, b) => P.endPos e b
  | Sum.inr i => P.portPos i

/-- the dart at a position -/
def dartAt (p : Pos V) : D (N := N) (k := k) :=
  match P.slotAt p with
  | Slot.edge e => if p = P.endPos e false then Sum.inl (e, false) else Sum.inl (e, true)
  | Slot.port i => Sum.inr i

theorem pos_dartAt (hP : P.Valid) (p : Pos V) : P.pos (P.dartAt p) = p := by
  obtain ⟨hend, -, hport, hcover⟩ := hP
  obtain ⟨hce, hcp⟩ := hcover p
  unfold dartAt
  cases h : P.slotAt p with
  | edge e =>
    by_cases hp : p = P.endPos e false
    · simp [hp, pos]
    · simp only [hp, if_false, pos]
      rcases hce e h with hc | hc
      · exact absurd hc hp
      · exact hc.symm
  | port i => simp [pos, hcp i h]

theorem dartAt_pos (hP : P.Valid) (d : D (N := N) (k := k)) : P.dartAt (P.pos d) = d := by
  obtain ⟨hend, hne, hport, hcover⟩ := hP
  rcases d with ⟨e, b⟩ | i
  · simp only [pos, dartAt, hend e b]
    cases b
    · simp
    · have : P.endPos e true ≠ P.endPos e false := fun h => hne e (congrArg Prod.fst h).symm
      simp [this]
  · simp [pos, dartAt, hport i]

/-- the position bijection -/
def posEquiv (hP : P.Valid) : D (N := N) (k := k) ≃ Pos V where
  toFun := P.pos
  invFun := P.dartAt
  left_inv := P.dartAt_pos hP
  right_inv := P.pos_dartAt hP

/-- the slot cycle at a vertex -/
def slotCycle : Equiv.Perm (Pos V) :=
  (Equiv.refl (Fin V)).prodCongr (Equiv.addRight (1 : Fin 3))

/-- the rotation: cycle the three slots of a vertex -/
def rho (hP : P.Valid) : Equiv.Perm (D (N := N) (k := k)) :=
  (P.posEquiv hP).trans (slotCycle.trans (P.posEquiv hP).symm)

theorem rho_apply (hP : P.Valid) (d : D (N := N) (k := k)) :
    P.rho hP d = P.dartAt (slotCycle (P.pos d)) := rfl

def vertOf (d : D (N := N) (k := k)) : Fin V := (P.pos d).1

theorem vertOf_rho (hP : P.Valid) (d : D (N := N) (k := k)) :
    P.vertOf (P.rho hP d) = P.vertOf d := by
  simp only [vertOf, rho_apply]
  rw [P.pos_dartAt hP]
  rfl

/-- the interior involution: swap the two ends of an edge -/
def alpha : Equiv.Perm (IDart (N := N)) :=
  (Equiv.refl (Fin N)).prodCongr (Function.Involutive.toPerm not Bool.not_not)

@[simp] theorem alpha_apply (e : Fin N) (b : Bool) : alpha (e, b) = (e, !b) := rfl

/-- **the cap of a valid presentation** -/
def toCap [NeZero k] (hP : P.Valid) :
    OpenTangleData (Fin V) (IDart (N := N)) (Fin k) where
  interiorVert := fun d => (P.endPos d.1 d.2).1
  boundaryVert := fun i => (P.portPos i).1
  interiorAlpha := alpha
  interiorAlpha_involutive := by rintro ⟨e, b⟩; cases b <;> rfl
  interiorAlpha_fixfree := by rintro ⟨e, b⟩; cases b <;> simp
  rho := P.rho hP
  vert_rho := fun d => by
    have h := P.vertOf_rho hP d
    rcases hd : P.rho hP d with ⟨e, b⟩ | i <;> rcases d with ⟨e', b'⟩ | i' <;>
      simp only [openTangleVertOf] <;> rw [hd] at h <;> exact h
  interior_no_self_loops := by
    rintro ⟨e, b⟩ h
    cases b
    · exact hP.2.1 e h
    · exact hP.2.1 e h.symm
  outer := Sum.inr 0

variable [NeZero k]

theorem toCap_vertOf (hP : P.Valid) (d : D (N := N) (k := k)) :
    (P.toCap hP).vertOf d = P.vertOf d := by
  rcases d with ⟨e, b⟩ | i <;> rfl

theorem toCap_rho (hP : P.Valid) : (P.toCap hP).rho = P.rho hP := rfl

/-! ## Cubicity and cyclic rotations hold for every valid presentation -/

/-- the darts at a vertex correspond to the three slots -/
noncomputable def dartsAtEquiv (hP : P.Valid) (v : Fin V) :
    {d : D (N := N) (k := k) // P.vertOf d = v} ≃ Fin 3 where
  toFun := fun d => (P.pos d.1).2
  invFun := fun s => ⟨P.dartAt (v, s), by
    show (P.pos (P.dartAt (v, s))).1 = v
    rw [P.pos_dartAt hP]⟩
  left_inv := fun d => by
    apply Subtype.ext
    show P.dartAt (v, (P.pos d.1).2) = d.1
    have hv : (P.pos d.1).1 = v := d.2
    have : (v, (P.pos d.1).2) = P.pos d.1 := Prod.ext hv.symm rfl
    rw [this, P.dartAt_pos hP]
  right_inv := fun s => by
    show (P.pos (P.dartAt (v, s))).2 = s
    rw [P.pos_dartAt hP]

theorem openIsCubic_toCap (hP : P.Valid) : OpenIsCubic (P.toCap hP) := by
  intro v
  have h1 : (openDartsAt (P.toCap hP) v).card =
      Fintype.card {d : D (N := N) (k := k) // P.vertOf d = v} := by
    rw [Fintype.card_subtype]
    unfold openDartsAt
    congr 1
    ext d
    simp [toCap_vertOf]
  rw [h1, Fintype.card_congr (P.dartsAtEquiv hP v)]
  simp

theorem slotCycle_pow_apply (n : Nat) (v : Fin V) (s : Fin 3) :
    (slotCycle ^ n) (v, s) = (v, (Equiv.addRight (1 : Fin 3) ^ n) s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, pow_succ', Equiv.Perm.mul_apply]
    rfl

omit [NeZero k] in
theorem rho_pow_apply (hP : P.Valid) (n : Nat) (d : D (N := N) (k := k)) :
    (P.rho hP ^ n) d = P.dartAt ((slotCycle ^ n) (P.pos d)) := by
  induction n with
  | zero => simp [P.dartAt_pos hP]
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, rho_apply, P.pos_dartAt hP, pow_succ',
      Equiv.Perm.mul_apply]

theorem exists_addRight_pow : ∀ s s' : Fin 3, ∃ n < 3, (Equiv.addRight (1 : Fin 3) ^ n) s = s' := by
  decide

theorem openRotationCyclic_toCap (hP : P.Valid) : OpenRotationCyclic (P.toCap hP) := by
  intro d d' hv
  rw [toCap_vertOf, toCap_vertOf] at hv
  obtain ⟨n, -, hn⟩ := exists_addRight_pow (P.pos d).2 (P.pos d').2
  refine ⟨n, ?_⟩
  rw [zpow_natCast, toCap_rho, rho_pow_apply]
  have hpos : (slotCycle ^ n) (P.pos d) = P.pos d' := by
    have := slotCycle_pow_apply n (P.pos d).1 (P.pos d).2
    rw [Prod.mk.eta] at this
    rw [this, hn]
    exact Prod.ext hv rfl
  rw [hpos, P.dartAt_pos hP]

end Pres

/-! ## Steps of the side multigraph, in terms of interior darts -/

section Steps

variable {Vt I B : Type*} [Fintype I] [DecidableEq I]

/-- one step along an interior edge -/
def InteriorStep (T : OpenTangleData Vt I B) (u v : Vt) : Prop :=
  ∃ d : I, T.interiorVert d = u ∧ T.interiorVert (T.interiorAlpha d) = v

/-- one step along an interior edge other than the edge of `d₀` -/
def InteriorStepAvoiding (T : OpenTangleData Vt I B) (d₀ : I) (u v : Vt) : Prop :=
  ∃ d : I, d ≠ d₀ ∧ d ≠ T.interiorAlpha d₀ ∧
    T.interiorVert d = u ∧ T.interiorVert (T.interiorAlpha d) = v

theorem interiorStep_symm {T : OpenTangleData Vt I B} {u v : Vt} (h : InteriorStep T u v) :
    InteriorStep T v u := by
  obtain ⟨d, h1, h2⟩ := h
  exact ⟨T.interiorAlpha d, h2, by rw [T.interiorAlpha_involutive]; exact h1⟩

theorem interiorStepAvoiding_symm {T : OpenTangleData Vt I B} {d₀ : I} {u v : Vt}
    (h : InteriorStepAvoiding T d₀ u v) : InteriorStepAvoiding T d₀ v u := by
  obtain ⟨d, hne1, hne2, h1, h2⟩ := h
  refine ⟨T.interiorAlpha d, ?_, ?_, h2, by rw [T.interiorAlpha_involutive]; exact h1⟩
  · intro h; apply hne2; rw [← h, T.interiorAlpha_involutive]
  · intro h; apply hne1; exact T.interiorAlpha.injective h

theorem sideEdgeOf_choose (T : OpenTangleData Vt I B) (e : SideEdge T) :
    sideEdgeOf T e.2.choose = e := by
  apply Subtype.ext
  exact e.2.choose_spec.symm

theorem sideEdgeOf_eq_iff (T : OpenTangleData Vt I B) (d d₀ : I) :
    sideEdgeOf T d = sideEdgeOf T d₀ ↔ d = d₀ ∨ d = T.interiorAlpha d₀ := by
  constructor
  · intro h
    have h' : s(d, T.interiorAlpha d) = s(d₀, T.interiorAlpha d₀) := congrArg Subtype.val h
    rcases Sym2.eq_iff.1 h' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · rfl
    · exact sideEdgeOf_alpha T d₀

theorem step_iff (T : OpenTangleData Vt I B) (u v : Vt) :
    (sideMultigraph T).Step u v ↔ InteriorStep T u v := by
  constructor
  · rintro ⟨e, -, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨e.2.choose, h1, h2⟩
    · exact interiorStep_symm ⟨e.2.choose, h1, h2⟩
  · rintro ⟨d, h1, h2⟩
    refine ⟨sideEdgeOf T d, not_false, ?_⟩
    rcases sideMultigraph_ends T d with ⟨hf, hs⟩ | ⟨hf, hs⟩
    · exact Or.inl ⟨hf.trans h1, hs.trans h2⟩
    · exact Or.inr ⟨hf.trans h2, hs.trans h1⟩

theorem stepAvoiding_iff (T : OpenTangleData Vt I B) (d₀ : I) (u v : Vt) :
    (sideMultigraph T).StepAvoiding (· = sideEdgeOf T d₀) u v ↔
      InteriorStepAvoiding T d₀ u v := by
  constructor
  · rintro ⟨e, hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · have hne' : ¬ (e.2.choose = d₀ ∨ e.2.choose = T.interiorAlpha d₀) := by
        rw [← sideEdgeOf_eq_iff, sideEdgeOf_choose]; exact hne
      exact ⟨e.2.choose, fun h => hne' (Or.inl h), fun h => hne' (Or.inr h), h1, h2⟩
    · have hne' : ¬ (e.2.choose = d₀ ∨ e.2.choose = T.interiorAlpha d₀) := by
        rw [← sideEdgeOf_eq_iff, sideEdgeOf_choose]; exact hne
      exact interiorStepAvoiding_symm
        ⟨e.2.choose, fun h => hne' (Or.inl h), fun h => hne' (Or.inr h), h1, h2⟩
  · rintro ⟨d, hne1, hne2, h1, h2⟩
    refine ⟨sideEdgeOf T d, ?_, ?_⟩
    · intro h
      rcases (sideEdgeOf_eq_iff T d d₀).1 h with h | h
      · exact hne1 h
      · exact hne2 h
    · rcases sideMultigraph_ends T d with ⟨hf, hs⟩ | ⟨hf, hs⟩
      · exact Or.inl ⟨hf.trans h1, hs.trans h2⟩
      · exact Or.inr ⟨hf.trans h2, hs.trans h1⟩

theorem reflTransGen_symm {α : Type*} {r : α → α → Prop} (hs : ∀ a b, r a b → r b a)
    {u v : α} (h : Relation.ReflTransGen r u v) : Relation.ReflTransGen r v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (hs _ _ hbc)).trans ih

theorem reach_iff (T : OpenTangleData Vt I B) (u v : Vt) :
    (sideMultigraph T).Reach u v ↔ Relation.ReflTransGen (InteriorStep T) u v :=
  ⟨Relation.ReflTransGen.mono fun a b => (step_iff T a b).1,
   Relation.ReflTransGen.mono fun a b => (step_iff T a b).2⟩

theorem reachAvoiding_iff (T : OpenTangleData Vt I B) (d₀ : I) (u v : Vt) :
    (sideMultigraph T).ReachAvoiding (sideEdgeOf T d₀) u v ↔
      Relation.ReflTransGen (InteriorStepAvoiding T d₀) u v :=
  ⟨Relation.ReflTransGen.mono fun a b => (stepAvoiding_iff T d₀ a b).1,
   Relation.ReflTransGen.mono fun a b => (stepAvoiding_iff T d₀ a b).2⟩

end Steps

namespace Pres

variable {V N k : Nat} (P : Pres V N k) [NeZero k]

/-! ## Connectivity and boundary-essentiality, decided -/

/-- Boolean interior adjacency -/
def adjB (u v : Fin V) : Bool :=
  (List.finRange N).any fun e =>
    decide ((P.endPos e false).1 = u ∧ (P.endPos e true).1 = v) ||
    decide ((P.endPos e true).1 = u ∧ (P.endPos e false).1 = v)

/-- Boolean interior adjacency avoiding the edge `e₀` -/
def adjAvoidB (e₀ : Fin N) (u v : Fin V) : Bool :=
  (List.finRange N).any fun e =>
    decide (e ≠ e₀) &&
    (decide ((P.endPos e false).1 = u ∧ (P.endPos e true).1 = v) ||
     decide ((P.endPos e true).1 = u ∧ (P.endPos e false).1 = v))

theorem adjB_iff (hP : P.Valid) (u v : Fin V) :
    P.adjB u v = true ↔ InteriorStep (P.toCap hP) u v := by
  simp only [adjB, List.any_eq_true, List.mem_finRange, true_and, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨(e, false), h1, h2⟩
    · exact ⟨(e, true), h1, h2⟩
  · rintro ⟨⟨e, b⟩, h1, h2⟩
    refine ⟨e, ?_⟩
    cases b
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

theorem adjAvoidB_iff (hP : P.Valid) (e₀ : Fin N) (b₀ : Bool) (u v : Fin V) :
    P.adjAvoidB e₀ u v = true ↔ InteriorStepAvoiding (P.toCap hP) (e₀, b₀) u v := by
  simp only [adjAvoidB, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨(e, false), ?_, ?_, h1, h2⟩
      · intro h; exact hne (congrArg Prod.fst h)
      · intro h; exact hne (congrArg Prod.fst h)
    · refine ⟨(e, true), ?_, ?_, h1, h2⟩
      · intro h; exact hne (congrArg Prod.fst h)
      · intro h; exact hne (congrArg Prod.fst h)
  · rintro ⟨⟨e, b⟩, hne1, hne2, h1, h2⟩
    refine ⟨e, ?_, ?_⟩
    · rintro rfl
      cases b <;> cases b₀
      · exact hne1 rfl
      · exact hne2 rfl
      · exact hne2 rfl
      · exact hne1 rfl
    · cases b
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩

theorem connected_of_allReach (hP : P.Valid) (h : allReach P.adjB = true) :
    (sideMultigraph (P.toCap hP)).Connected := by
  intro u v
  rw [reach_iff]
  exact Relation.ReflTransGen.mono (fun a b hab => (P.adjB_iff hP a b).1 hab)
    (reflTransGen_of_allReach P.adjB h u v)

/-- every bridge of the cap has a port on each side -/
def essentialCheck : Bool :=
  (List.finRange N).all fun e₀ =>
    decide ((P.endPos e₀ true).1 ∈ reachFrom (P.adjAvoidB e₀) (P.endPos e₀ false).1) ||
      ((List.finRange k).any (fun i =>
          decide ((P.portPos i).1 ∈ reachFrom (P.adjAvoidB e₀) (P.endPos e₀ false).1)) &&
       (List.finRange k).any (fun i =>
          decide ((P.portPos i).1 ∈ reachFrom (P.adjAvoidB e₀) (P.endPos e₀ true).1)))

theorem reachAvoiding_of_mem_reachFrom (hP : P.Valid) (e₀ : Fin N) (b₀ : Bool) {u v : Fin V}
    (h : v ∈ reachFrom (P.adjAvoidB e₀) u) :
    (sideMultigraph (P.toCap hP)).ReachAvoiding (sideEdgeOf (P.toCap hP) (e₀, b₀)) u v := by
  rw [reachAvoiding_iff]
  exact Relation.ReflTransGen.mono (fun a b hab => (P.adjAvoidB_iff hP e₀ b₀ a b).1 hab)
    ((mem_reachFrom_iff _ u v).1 h)

theorem reachAvoiding_symm (hP : P.Valid) (e₀ : Fin N) (b₀ : Bool) {u v : Fin V}
    (h : (sideMultigraph (P.toCap hP)).ReachAvoiding (sideEdgeOf (P.toCap hP) (e₀, b₀)) u v) :
    (sideMultigraph (P.toCap hP)).ReachAvoiding (sideEdgeOf (P.toCap hP) (e₀, b₀)) v u := by
  rw [reachAvoiding_iff] at h ⊢
  exact reflTransGen_symm (fun _ _ => interiorStepAvoiding_symm) h

theorem boundaryEssential_of_check (hP : P.Valid) (h : P.essentialCheck = true)
    {Pt : Type*} (portV : Pt → Fin V)
    (hport : ∀ i : Fin k, ∃ p : Pt, portV p = (P.portPos i).1) :
    BoundaryEssential (sideMultigraph (P.toCap hP)) portV := by
  intro e hbridge
  obtain ⟨⟨e₀, b₀⟩, hd⟩ : ∃ d, d = e.2.choose := ⟨_, rfl⟩
  have he : e = sideEdgeOf (P.toCap hP) (e₀, b₀) := by
    rw [hd]; exact (sideEdgeOf_choose _ e).symm
  simp only [essentialCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  have hfst : (sideMultigraph (P.toCap hP)).fst e = (P.endPos e₀ b₀).1 := by
    show (P.toCap hP).interiorVert e.2.choose = _
    rw [← hd]; rfl
  have hsnd : (sideMultigraph (P.toCap hP)).snd e = (P.endPos e₀ (!b₀)).1 := by
    show (P.toCap hP).interiorVert ((P.toCap hP).interiorAlpha e.2.choose) = _
    rw [← hd]; rfl
  rw [hfst, hsnd, he]
  rcases h e₀ with hreach | ⟨⟨i, -, hi⟩, ⟨j, -, hj⟩⟩
  · exfalso
    apply hbridge
    rw [hfst, hsnd, he]
    have hr := P.reachAvoiding_of_mem_reachFrom hP e₀ b₀ hreach
    cases b₀
    · exact hr
    · exact P.reachAvoiding_symm hP e₀ true hr
  · obtain ⟨p, hp⟩ := hport i
    obtain ⟨q, hq⟩ := hport j
    have hi' := P.reachAvoiding_of_mem_reachFrom hP e₀ b₀ hi
    have hj' := P.reachAvoiding_of_mem_reachFrom hP e₀ b₀ hj
    rw [← hp] at hi'
    rw [← hq] at hj'
    cases b₀
    · exact ⟨⟨p, hi'⟩, ⟨q, hj'⟩⟩
    · exact ⟨⟨q, hj'⟩, ⟨p, hi'⟩⟩

/-! ## Hub faces and the Euler count, decided -/

/-- an injective index on the hub carrier -/
def hubIdx : (IDart (N := N) ⊕ Fin k) ⊕ Fin k → Nat
  | Sum.inl (Sum.inl (e, b)) => 2 * e.val + (if b then 1 else 0)
  | Sum.inl (Sum.inr i) => 2 * N + i.val
  | Sum.inr i => 2 * N + k + i.val

omit P [NeZero k] in
theorem hubIdx_injective : Function.Injective (hubIdx (N := N) (k := k)) := by
  rintro ((⟨e, b⟩ | i) | i) ((⟨e', b'⟩ | i') | i') h <;> simp only [hubIdx] at h
  · have he : e.val = e'.val := by cases b <;> cases b' <;> simp at h <;> omega
    have hb : b = b' := by
      cases b <;> cases b' <;> first | rfl | (exfalso; simp at h <;> omega)
    rw [Fin.ext he, hb]
  · exfalso; have := e.isLt; split_ifs at h <;> omega
  · exfalso; have := e.isLt; split_ifs at h <;> omega
  · exfalso; have := e'.isLt; split_ifs at h <;> omega
  · rw [Fin.ext (by omega : i.val = i'.val)]
  · exfalso; have := i.isLt; omega
  · exfalso; have := e'.isLt; split_ifs at h <;> omega
  · exfalso; have := i'.isLt; omega
  · rw [Fin.ext (by omega : i.val = i'.val)]

/-- no hub face passes the hub twice -/
def facesDistinctCheck (hP : P.Valid) : Bool :=
  (List.finRange k).all fun b =>
    (orbitList (hubPhi (P.toCap hP) (finRotate k)) (Sum.inr b)).all fun y =>
      match y with
      | Sum.inr b' => decide (b' = b)
      | _ => true

theorem hubFacesDistinct_of_check (hP : P.Valid) (h : P.facesDistinctCheck hP = true) :
    HubFacesDistinct (P.toCap hP) (finRotate k) := by
  intro b b' hsc
  simp only [facesDistinctCheck, List.all_eq_true, List.mem_finRange, true_implies] at h
  have := h b (Sum.inr b') ((mem_orbitList_iff _ _ _).2 hsc)
  simp only [decide_eq_true_eq] at this
  exact this.symm

/-- the spherical Euler count of the hub closure -/
def sphericalCheck (hP : P.Valid) : Bool :=
  decide (V + 1 + cycleCount hubIdx (hubPhi (P.toCap hP) (finRotate k)) =
    cycleCount hubIdx (hubAlpha (P.toCap hP)) + 2)

theorem closedSideSpherical_of_check (hP : P.Valid) (h : P.sphericalCheck hP = true) :
    ClosedSideSpherical (P.toCap hP) (finRotate k) := by
  unfold ClosedSideSpherical
  have h' := of_decide_eq_true h
  rw [cycleCount_eq_orbitCount _ hubIdx_injective, cycleCount_eq_orbitCount _ hubIdx_injective]
    at h'
  simpa using h'

/-! ## The disc package -/

/-- all four decided disc facts -/
def discCheck (hP : P.Valid) : Bool :=
  allReach P.adjB && P.essentialCheck && P.facesDistinctCheck hP && P.sphericalCheck hP

open CapExclusion GoertzelV24VertexSideOpenTangle GoertzelV24RetainedRegionBoundaryOrder
  GoertzelV24RotationCutDartDecomposition in
/-- When the cap's ports are the shore's boundary darts in facial cyclic order, the forced
hub rotation is the port rotation. -/
theorem capHubRotation_eq_finRotate {Vg Eg : Type*} [Fintype Vg] [DecidableEq Vg]
    [Fintype Eg] [DecidableEq Eg]
    (RS : RotationSystem Vg Eg) (keep : Vg → Prop) {n : Nat}
    (order : Fin n ≃ BoundaryDart RS keep)
    (hsuccessor : order.permCongr (finRotate n) = retainedRegionBoundarySuccessor RS keep) :
    capHubRotation RS keep order.symm = finRotate n := by
  ext i
  have h := congrArg (fun σ => σ (order i)) hsuccessor
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h
  simp [capHubRotation, canonicalHubRotation, Equiv.Perm.inv_def, ← h]

open CapExclusion GoertzelV24RotationCutDartDecomposition in
/-- **A presented cap passing the check is a disc on the shore's ports.** -/
theorem capDiscData_of_discCheck {Vg Eg : Type*} [Fintype Vg] [DecidableEq Vg]
    [Fintype Eg] [DecidableEq Eg]
    (RS : RotationSystem Vg Eg) (keep : Vg → Prop)
    (matching : BoundaryDart RS keep ≃ Fin k)
    (hrot : capHubRotation RS keep matching = finRotate k)
    (hP : P.Valid) (h : P.discCheck hP = true) :
    CapDiscData RS keep (P.toCap hP) matching := by
  simp only [discCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact
    { cubic := P.openIsCubic_toCap hP
      rotation := P.openRotationCyclic_toCap hP
      connected := P.connected_of_allReach hP h1
      essential := P.boundaryEssential_of_check hP h2 _ fun i =>
        ⟨matching.symm i, by
          show (P.portPos (matching (matching.symm i))).1 = _
          rw [Equiv.apply_symm_apply]⟩
      facesDistinct := by rw [hrot]; exact P.hubFacesDistinct_of_check hP h3
      spherical := by rw [hrot]; exact P.closedSideSpherical_of_check hP h4 }

end Pres

end PresentedCap
end KempeDerivation
end Mettapedia.GraphTheory.FourColor
