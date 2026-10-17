import Mettapedia.SetTheory.OpenTower.AntiFounded.AFAStages
import Mettapedia.SetTheory.OpenTower.AntiFounded.Size

/-!
# Height `ω` under anti-foundation: the rational hypersets

A hyperset is *rational* when it is the picture of a graph with finitely many nodes
(`FinitePicture`). The rational hypersets form a hyperset `R_ω` (`rational`, `mem_rational`).

**`R_ω` is the least nonempty stage closed under anti-foundation.** It is a closed stage
(`hclosed_rational`): the union, the power set and the finite replacements of finitely pictured
hypersets are finitely pictured, by explicit graphs (`sUnion_mk`, `powerset_mk`,
`finitePicture_of_finite_family`). It is closed under anti-foundation (`afaClosed_rational`),
since a graph whose nodes inject into the finitely many members of a member is finite. Its
well-founded part is `V_ω` (`toZFSet_rational`). And every nonempty stage closed under
anti-foundation includes it (`AFAClosed.rational_subset`): a finite graph injects into the
members of a finite ordinal.

**At height `ω` the stage closed under anti-foundation is not unique.** `R_ω` and `B_ℵ₀` are
both closed under anti-foundation with well-founded part `V_ω`, and they differ
(`rational_ne_branching`): the stream of the perfect squares is hereditarily finitely branching
but has no finite picture (`streamAt_squares_not_rational`), because its tails are pairwise
distinct (`streamAt_squares_injective`). So among stages closed under anti-foundation the fibre
of the height map over `ω` is the interval from `R_ω` to `B_ℵ₀`
(`afaClosed_fibre_omega`), while over each inaccessible height it is a single stage
(`afaClosed_iff_eq_branching`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.AntiFounded

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation
open Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
open Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph
open Cardinal
open scoped ZFSet

universe u

/-! ## Finite pictures -/

/-- `x` is the picture of a graph with finitely many nodes. -/
def FinitePicture (x : HSet.{u}) : Prop :=
  ∃ G : AccessiblePointedGraph.{u}, Finite G.Node ∧ HSet.mk G = x

theorem finitePicture_decorate {α : Type u} [Finite α] (r : α → α → Prop) (a : α) :
    FinitePicture (HSet.decorate r a) :=
  ⟨generated r a, Subtype.finite, rfl⟩

theorem FinitePicture.mem {x y : HSet.{u}} (hx : FinitePicture x) (hy : y ∈ x) :
    FinitePicture y := by
  obtain ⟨G, hG, rfl⟩ := hx
  obtain ⟨c, _, rfl⟩ := HSet.mem_mk.mp hy
  exact finitePicture_decorate G.edge c

theorem FinitePicture.herSmall {x : HSet.{u}} (hx : FinitePicture x) : HerSmall ℵ₀ x := by
  obtain ⟨G, hG, rfl⟩ := hx
  exact herSmall_mk G (lt_aleph0_of_finite _)

theorem finitePicture_empty : FinitePicture (∅ : HSet.{u}) := by
  have equal : HSet.decorate (fun _ _ : PUnit.{u + 1} => False) PUnit.unit = ∅ :=
    HSet.eq_empty_iff.mpr fun _ hz => by
      obtain ⟨_, h, _⟩ := HSet.mem_decorate.mp hz
      exact h
  rw [← equal]
  exact finitePicture_decorate _ _

/-! ## Union, power set and finite replacement of finite pictures -/

/-- The union graph: a new point whose children are the grandchildren of the old point. -/
def unionEdge (G : AccessiblePointedGraph.{u}) : Option G.Node → Option G.Node → Prop
  | none, some m => ∃ c, G.edge G.point c ∧ G.edge c m
  | some n, some m => G.edge n m
  | _, none => False

theorem decorate_unionEdge_some (G : AccessiblePointedGraph.{u}) (n : G.Node) :
    HSet.decorate (unionEdge G) (some n) = HSet.decorate G.edge n := by
  refine (HSet.decorate_eq_of_bisimilar (bisimilar_apply (r := G.edge) (s := unionEdge G)
    (f := some) (fun _ _ h => h) (fun n b h => ?_) n)).symm
  cases b with
  | none => exact h.elim
  | some m => exact ⟨m, h, rfl⟩

theorem sUnion_mk (G : AccessiblePointedGraph.{u}) :
    HSet.sUnion (HSet.mk G) = HSet.decorate (unionEdge G) none := by
  apply HSet.ext
  intro z
  rw [HSet.mem_sUnion, HSet.mem_decorate]
  constructor
  · rintro ⟨w, hw, hz⟩
    obtain ⟨c, hc, rfl⟩ := HSet.mem_mk.mp hw
    obtain ⟨m, hm, rfl⟩ := HSet.mem_decorate.mp hz
    exact ⟨some m, ⟨c, hc, hm⟩, decorate_unionEdge_some G m⟩
  · rintro ⟨b, hb, rfl⟩
    cases b with
    | none => exact hb.elim
    | some m =>
      obtain ⟨c, hc, hm⟩ := hb
      refine ⟨HSet.decorate G.edge c, HSet.mem_mk.mpr ⟨c, hc, rfl⟩, ?_⟩
      rw [decorate_unionEdge_some]
      exact HSet.decorate_mem_decorate hm

/-- The power set graph: a new point whose children are the sets of children of the old
point. -/
def powerEdge (G : AccessiblePointedGraph.{u}) :
    Option (Set G.Node ⊕ G.Node) → Option (Set G.Node ⊕ G.Node) → Prop
  | none, some (.inl S) => ∀ c ∈ S, G.edge G.point c
  | some (.inl S), some (.inr c) => c ∈ S
  | some (.inr n), some (.inr m) => G.edge n m
  | _, _ => False

theorem decorate_powerEdge_inr (G : AccessiblePointedGraph.{u}) (n : G.Node) :
    HSet.decorate (powerEdge G) (some (.inr n)) = HSet.decorate G.edge n := by
  refine (HSet.decorate_eq_of_bisimilar (bisimilar_apply (r := G.edge) (s := powerEdge G)
    (f := fun n => some (.inr n)) (fun _ _ h => h) (fun n b h => ?_) n)).symm
  rcases b with _ | _ | m
  · exact h.elim
  · exact h.elim
  · exact ⟨m, h, rfl⟩

theorem mem_decorate_powerEdge_inl {G : AccessiblePointedGraph.{u}} {S : Set G.Node}
    {w : HSet.{u}} :
    w ∈ HSet.decorate (powerEdge G) (some (.inl S)) ↔ ∃ c ∈ S, HSet.decorate G.edge c = w := by
  rw [HSet.mem_decorate]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases b with _ | _ | c
    · exact hb.elim
    · exact hb.elim
    · exact ⟨c, hb, (decorate_powerEdge_inr G c).symm⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨some (.inr c), hc, decorate_powerEdge_inr G c⟩

theorem powerset_mk (G : AccessiblePointedGraph.{u}) :
    HSet.powerset (HSet.mk G) = HSet.decorate (powerEdge G) none := by
  classical
  apply HSet.ext
  intro z
  rw [HSet.mem_powerset, HSet.mem_decorate]
  constructor
  · intro hz
    refine ⟨some (.inl {c | G.edge G.point c ∧ HSet.decorate G.edge c ∈ z}),
      fun c hc => hc.1, ?_⟩
    apply HSet.ext
    intro w
    rw [mem_decorate_powerEdge_inl]
    constructor
    · rintro ⟨c, ⟨_, hcz⟩, rfl⟩
      exact hcz
    · intro hw
      obtain ⟨c, hc, rfl⟩ := HSet.mem_mk.mp (HSet.subset_iff.mp hz hw)
      exact ⟨c, ⟨hc, hw⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    rcases b with _ | S | _
    · exact hb.elim
    · refine HSet.subset_iff.mpr fun w hw => ?_
      obtain ⟨c, hc, rfl⟩ := mem_decorate_powerEdge_inl.mp hw
      exact HSet.mem_mk.mpr ⟨c, hb c hc, rfl⟩
    · exact hb.elim

/-- A hyperset whose members are finitely many finitely pictured hypersets is finitely
pictured. -/
theorem finitePicture_of_finite_family {ι : Type u} [Finite ι] {g : ι → HSet.{u}}
    (hg : ∀ i, FinitePicture (g i)) {b : HSet.{u}} (hb : ∀ y, y ∈ b ↔ ∃ i, g i = y) :
    FinitePicture b := by
  choose G hG hGg using hg
  have : ∀ i, Finite (G i).Node := hG
  refine ⟨sup G, show Finite (Option (Σ i, (G i).Node)) from inferInstance, ?_⟩
  apply HSet.ext
  intro y
  change y ∈ HSet.range G ↔ y ∈ b
  rw [HSet.mem_range, hb]
  simp only [hGg]

/-! ## The stage `R_ω` -/

/-- The hyperset of the rational hypersets. -/
noncomputable def rational : HSet.{u} :=
  HSet.sep FinitePicture (branching ℵ₀)

theorem mem_rational {y : HSet.{u}} : y ∈ rational ↔ FinitePicture y := by
  rw [rational, HSet.mem_sep, mem_branching]
  exact ⟨fun h => h.2, fun h => ⟨h.herSmall, h⟩⟩

theorem rational_subset_branching : rational.{u} ⊆ branching ℵ₀ :=
  HSet.subset_iff.mpr fun _ hy => mem_branching.mpr (mem_rational.mp hy).herSmall

/-- A finitely pictured hyperset has finitely many members, presented without repetition. -/
theorem FinitePicture.exists_finite_members {x : HSet.{u}} (hx : FinitePicture x) :
    ∃ (ι : Type u) (g : ι → HSet.{u}), Finite ι ∧ Function.Injective g ∧
      ∀ y, y ∈ x ↔ ∃ i, g i = y := by
  obtain ⟨ι, g, hg, hxg⟩ := exists_injective_members x
  have small := (smallMembers_iff_of_injective hg hxg).mp hx.herSmall.smallMembers
  exact ⟨ι, g, lt_aleph0_iff_finite.mp small, hg, hxg⟩

/-- **`R_ω` is a closed stage.** -/
theorem hclosed_rational : HClosed rational.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact mem_rational.mpr ((mem_rational.mp hx).mem hy)
  · intro x hx
    obtain ⟨G, hG, rfl⟩ := mem_rational.mp hx
    rw [sUnion_mk]
    exact mem_rational.mpr (finitePicture_decorate _ _)
  · intro x hx
    obtain ⟨G, hG, rfl⟩ := mem_rational.mp hx
    rw [powerset_mk]
    exact mem_rational.mpr (finitePicture_decorate _ _)
  · rintro a b ha hb ⟨f, hf⟩
    obtain ⟨ι, g, hfin, _, hag⟩ := (mem_rational.mp ha).exists_finite_members
    refine mem_rational.mpr (finitePicture_of_finite_family (g := fun i => f (g i))
      (fun i => mem_rational.mp (hb ((hf _).mpr ⟨g i, (hag _).mpr ⟨i, rfl⟩, rfl⟩))) fun y => ?_)
    rw [hf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, rfl⟩ := (hag x).mp hx
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨g i, (hag _).mpr ⟨i, rfl⟩, rfl⟩

/-- **`R_ω` is closed under anti-foundation.** -/
theorem afaClosed_rational : AFAClosed rational.{u} := by
  refine ⟨hclosed_rational, ?_⟩
  intro x hx α r ⟨g, injective, hg⟩ a
  obtain ⟨ι, g', hfin, hg', hxg'⟩ := (mem_rational.mp hx).exists_finite_members
  have hit : ∀ b, ∃ i, g' i = g b := fun b => (hxg' _).mp (hg b)
  choose φ hφ using hit
  have φinjective : Function.Injective φ := fun b b' e =>
    injective ((hφ b).symm.trans ((congrArg g' e).trans (hφ b')))
  have : Finite α := Finite.of_injective φ φinjective
  exact mem_rational.mpr (finitePicture_decorate r a)

theorem empty_mem_rational : (∅ : HSet.{u}) ∈ rational :=
  mem_rational.mpr finitePicture_empty

/-- **The well-founded part of `R_ω` is `V_ω`.** -/
theorem toZFSet_rational : HSet.toZFSet rational.{u} = V_ Ordinal.omega0 := by
  have hW := hclosed_rational.closed_toZFSet
  have inside : HSet.toZFSet rational.{u} ⊆ V_ Ordinal.omega0 := by
    rw [← toZFSet_branching_aleph0]
    exact toZFSet_mono rational_subset_branching
  have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet rational := by
    rw [mem_toZFSet_iff, HSet.ofZFSet_empty]
    exact empty_mem_rational
  have rankEq : (HSet.toZFSet rational.{u}).rank = Ordinal.omega0 :=
    le_antisymm (ZFSet.subset_vonNeumann.mp inside) (omega_le_rank hW hEmpty)
  rw [closed_eq_vonNeumann hW, rankEq]

/-! ## `R_ω` is the least nonempty stage closed under anti-foundation -/

/-- A graph lies in a stage closed under anti-foundation as soon as the stage holds the finite
or infinite ordinal counting its nodes. -/
theorem AFAClosed.mk_mem {U : HSet.{u}} (hU : AFAClosed U) (G : AccessiblePointedGraph.{u})
    (hx : HSet.ofZFSet (#G.Node).ord.toZFSet ∈ U) : HSet.mk G ∈ U := by
  obtain ⟨e⟩ := Cardinal.eq.mp (mk_ord_toType #G.Node).symm
  let g : G.Node → HSet.{u} := fun n =>
    HSet.ofZFSet ((Ordinal.typein (α := (#G.Node).ord.ToType) (· < ·)).toRelEmbedding
      (e n)).toZFSet
  have injective : Function.Injective g := fun n n' equal =>
    e.injective (Ordinal.typein_injective _
      (Ordinal.toZFSet_injective (HSet.ofZFSet_injective equal)))
  have members : ∀ n, g n ∈ HSet.ofZFSet (#G.Node).ord.toZFSet := fun n =>
    HSet.ofZFSet_mem_ofZFSet_iff.mpr
      (Ordinal.mem_toZFSet_iff.mpr ⟨_, Ordinal.typein_lt_self _, rfl⟩)
  have decorated := hU.decorate_mem hx G.edge ⟨g, injective, members⟩ G.point
  rwa [← HSet.mk_eq_decorate] at decorated

/-- **Every nonempty stage closed under anti-foundation includes `R_ω`.** -/
theorem AFAClosed.rational_subset {U : HSet.{u}} (hU : AFAClosed U) {x : HSet.{u}}
    (hx : x ∈ U) : rational ⊆ U := by
  have hW := hU.toHClosed.closed_toZFSet
  have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet U := by
    rw [mem_toZFSet_iff, HSet.ofZFSet_empty]
    exact hU.toHClosed.empty_mem hx
  have height := omega_le_rank hW hEmpty
  refine HSet.subset_iff.mpr fun y hy => ?_
  obtain ⟨G, hG, rfl⟩ := mem_rational.mp hy
  refine hU.mk_mem G (mem_toZFSet_iff.mp ?_)
  rw [closed_eq_vonNeumann hW, ZFSet.mem_vonNeumann, Ordinal.rank_toZFSet]
  refine lt_of_lt_of_le ?_ height
  rw [← ord_aleph0]
  exact ord_lt_ord.mpr (lt_aleph0_of_finite _)

/-! ## `R_ω` is not `B_ℵ₀` -/

/-- The perfect squares. -/
def squares : Set ℕ := {n | ∃ t, t * t = n}

theorem streamAt_eq_shift {A A' : Set ℕ} {m n : ℕ}
    (h : streamAt.{u} A m = streamAt A' n) : ∀ k, streamAt.{u} A (m + k) = streamAt A' (n + k)
  | 0 => h
  | k + 1 => by
    have member : streamAt.{u} A (m + k + 1) ∈ streamAt A' (n + k) := by
      rw [← streamAt_eq_shift h k]
      exact streamAt_succ_mem _
    rcases mem_streamAt.mp member with e | ⟨_, e⟩
    · exact e
    · exact absurd e (streamAt_ne_empty _)

theorem streamAt_squares_lt_ne {m n : ℕ} (hmn : m < n) :
    streamAt.{u} squares m ≠ streamAt squares n := by
  intro h
  have hs : n ≤ n * n := Nat.le_mul_self n
  have square : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
  obtain ⟨s, hs_eq⟩ : ∃ s, s = n * n := ⟨_, rfl⟩
  rw [← hs_eq] at hs square
  have shift := streamAt_eq_shift h (s - m)
  have inLeft : m + (s - m) ∈ squares := ⟨n, by rw [← hs_eq]; omega⟩
  have inRight : n + (s - m) ∈ squares := by
    have e : (∅ : HSet.{u}) ∈ streamAt squares (n + (s - m)) := by
      rw [← shift]
      exact empty_mem_streamAt_iff.mpr inLeft
    exact empty_mem_streamAt_iff.mp e
  exact Nat.not_exists_sq (m := n) (by rw [← hs_eq]; omega) (by rw [square]; omega) inRight

/-- **The tails of the stream of squares are pairwise distinct.** -/
theorem streamAt_squares_injective : Function.Injective (streamAt.{u} squares) := by
  intro m n h
  rcases lt_trichotomy m n with hlt | heq | hgt
  · exact absurd h (streamAt_squares_lt_ne hlt)
  · exact heq
  · exact absurd h.symm (streamAt_squares_lt_ne hgt)

theorem below_streamAt_of_le {A : Set ℕ} (k : ℕ) : Below (streamAt.{u} A 0) (streamAt A k) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact ih.tail (streamAt_succ_mem k)

/-- **The stream of squares has no finite picture.** -/
theorem streamAt_squares_not_rational : ¬ FinitePicture (streamAt.{u} squares 0) := by
  rintro ⟨G, hG, hGx⟩
  have node : ∀ k, ∃ n, HSet.decorate G.edge n = streamAt.{u} squares k := fun k =>
    below_mk (hGx ▸ below_streamAt_of_le k)
  choose φ hφ using node
  have injective : Function.Injective φ := fun k k' e =>
    streamAt_squares_injective ((hφ k).symm.trans ((congrArg _ e).trans (hφ k')))
  have : Finite ℕ := Finite.of_injective φ injective
  exact not_finite ℕ

/-- **`R_ω` and `B_ℵ₀` differ.** -/
theorem rational_ne_branching : rational.{u} ≠ branching ℵ₀ := by
  intro equal
  have member := stream_mem_branching.{u} squares
  rw [← equal, mem_rational] at member
  exact streamAt_squares_not_rational member

/-- **The fibre over `ω` among stages closed under anti-foundation.** `R_ω` and `B_ℵ₀` are
closed under anti-foundation with well-founded part `V_ω`, they differ, and every stage closed
under anti-foundation with well-founded part `V_ω` lies between them. -/
theorem afaClosed_fibre_omega :
    AFAClosed rational.{u} ∧ AFAClosed (branching (ℵ₀ : Cardinal.{u})) ∧
      HSet.toZFSet rational.{u} = V_ Ordinal.omega0 ∧
      HSet.toZFSet (branching (ℵ₀ : Cardinal.{u})) = V_ Ordinal.omega0 ∧
      rational.{u} ≠ branching ℵ₀ ∧
      ∀ U : HSet.{u}, AFAClosed U → HSet.toZFSet U = V_ Ordinal.omega0 →
        rational ⊆ U ∧ U ⊆ branching ℵ₀ := by
  refine ⟨afaClosed_rational, afaClosed_branching (Or.inl rfl), toZFSet_rational,
    toZFSet_branching_aleph0, rational_ne_branching, fun U hU hW => ⟨?_, ?_⟩⟩
  · have hEmpty : (∅ : ZFSet.{u}) ∈ HSet.toZFSet U := by
      rw [hW, ZFSet.mem_vonNeumann, ZFSet.rank_empty]
      exact Ordinal.omega0_pos
    have member : HSet.ofZFSet ∅ ∈ U := mem_toZFSet_iff.mp hEmpty
    rw [HSet.ofZFSet_empty] at member
    exact hU.rational_subset member
  · refine HSet.subset_iff.mpr fun y hy => mem_branching.mpr fun z hz => ?_
    have hW' : HSet.toZFSet U = V_ (ℵ₀ : Cardinal.{u}).ord := by rw [hW, ord_aleph0]
    exact hU.toHClosed.smallMembers_of_mem hW' aleph0_ne_zero
      (hU.toHClosed.mem_of_reflTransGen hy hz)

#print axioms hclosed_rational
#print axioms afaClosed_rational
#print axioms toZFSet_rational
#print axioms AFAClosed.rational_subset
#print axioms streamAt_squares_injective
#print axioms rational_ne_branching
#print axioms afaClosed_fibre_omega

end Mettapedia.SetTheory.OpenTower.AntiFounded
