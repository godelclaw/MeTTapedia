import Mathlib.Order.Category.Preord
import Mettapedia.Logic.WorldModel.Indexed.SourceExample

/-!
# Extension necessity on a base of worlds

On any base category, `extBox P b` holds when `P` holds at every world `b`
extends to, and `extDiamond P b` when it holds at some.

* S4 from identities and composition: `extBox_T`, `extBox_four`, `extBox_K`,
  necessitation, upward persistence, and the duality with the diamond.
* `.2` on a directed base (`extBox_dot2`), `.3` on a base whose extensions of a
  world are comparable (`extBox_dot3`).
* Controls: on the fork `root → left, root → right` both `.2` and `.3` fail
  (`fork_not_dot2`, `fork_not_dot3`); on the diamond, which is directed, `.2`
  holds and `.3` fails (`diamond_dot2`, `diamond_not_dot3`).
* The source worlds are directed (`sources_directed`), so `.2` holds there, and
  with two sources `.3` fails (`sources_not_dot3`).

Three relations stay apart on the source example: world extension (inclusion
of worlds), epistemic access at a world (equal profiles there) and operational
reachability (revision by further records).  Epistemic access is symmetric and
shrinks along extension (`epistemic_antitone`); reachability is not symmetric
(`reachability_not_symmetric`); neither contains the other
(`epistemic_not_reachable`, `reachable_not_epistemic`).
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Logic.WorldModel.Indexed.Modal

universe vB uB

section Frames

variable {B : Type uB} [Category.{vB} B]

/-- Extension necessity: `P` holds at every extension. -/
def extBox (P : B → Prop) (b : B) : Prop := ∀ (c : B) (_ : b ⟶ c), P c

/-- Extension possibility: `P` holds at some extension. -/
def extDiamond (P : B → Prop) (b : B) : Prop := ∃ (c : B) (_ : b ⟶ c), P c

variable {P R : B → Prop} {b : B}

/-- T, from identities. -/
theorem extBox_T (h : extBox P b) : P b := h b (𝟙 b)

/-- 4, from composition. -/
theorem extBox_four (h : extBox P b) : extBox (extBox P) b :=
  fun _ f _ g => h _ (f ≫ g)

/-- K. -/
theorem extBox_K (himp : extBox (fun c => P c → R c) b) (h : extBox P b) : extBox R b :=
  fun c f => himp c f (h c f)

/-- Necessitation. -/
theorem extBox_of_forall (h : ∀ c, P c) (b : B) : extBox P b := fun c _ => h c

/-- Necessity persists along extension. -/
theorem extBox_persist {c : B} (h : extBox P b) (f : b ⟶ c) : extBox P c :=
  fun d g => h d (f ≫ g)

/-- The diamond is the dual of the box. -/
theorem extDiamond_iff_not_extBox_not : extDiamond P b ↔ ¬ extBox (fun c => ¬ P c) b := by
  constructor
  · rintro ⟨c, f, hc⟩ h
    exact h c f hc
  · intro h
    by_contra hd
    exact h fun c f hc => hd ⟨c, f, hc⟩

/-- A base is directed when any two extensions of a world have a common
extension. -/
def Directed (B : Type uB) [Category.{vB} B] : Prop :=
  ∀ (b c d : B) (_ : b ⟶ c) (_ : b ⟶ d), ∃ e, Nonempty (c ⟶ e) ∧ Nonempty (d ⟶ e)

/-- Any two extensions of a world are comparable. -/
def ExtensionsComparable (B : Type uB) [Category.{vB} B] : Prop :=
  ∀ (b c d : B) (_ : b ⟶ c) (_ : b ⟶ d), Nonempty (c ⟶ d) ∨ Nonempty (d ⟶ c)

/-- `.2` on a directed base. -/
theorem extBox_dot2 (directed : Directed B) (h : extDiamond (extBox P) b) :
    extBox (extDiamond P) b := by
  obtain ⟨c, f, hc⟩ := h
  intro d g
  obtain ⟨e, ⟨k⟩, ⟨l⟩⟩ := directed b c d f g
  exact ⟨e, l, hc e k⟩

/-- `.3` on a base whose extensions of each world are comparable. -/
theorem extBox_dot3 (comparable : ExtensionsComparable B) (b : B) :
    extBox (fun c => extBox P c → R c) b ∨ extBox (fun c => extBox R c → P c) b := by
  by_contra both
  rw [not_or] at both
  obtain ⟨h1, h2⟩ := both
  simp only [extBox, not_forall] at h1 h2
  obtain ⟨c, f, hPc, hRc⟩ := h1
  obtain ⟨d, g, hRd, hPd⟩ := h2
  rcases comparable b c d f g with k | k
  · exact hPd (hPc d k.some)
  · exact hRc (hRd c k.some)

end Frames

/-! ## Controls -/

/-- The fork: a root with two incomparable extensions. -/
inductive Fork
  | root
  | left
  | right
  deriving DecidableEq

/-- The diamond: the fork with a common top. -/
inductive Diamond
  | root
  | left
  | right
  | top
  deriving DecidableEq

/-- The order of the fork. -/
def Fork.le : Fork → Fork → Bool
  | .root, _ => true
  | .left, .left => true
  | .right, .right => true
  | _, _ => false

/-- The order of the diamond. -/
def Diamond.le : Diamond → Diamond → Bool
  | .root, _ => true
  | .left, .left => true
  | .left, .top => true
  | .right, .right => true
  | .right, .top => true
  | .top, .top => true
  | _, _ => false

instance : Preorder Fork where
  le a b := Fork.le a b = true
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [Fork.le]

instance : Preorder Diamond where
  le a b := Diamond.le a b = true
  le_refl a := by cases a <;> rfl
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp [Diamond.le]

instance : DecidableRel (α := Fork) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (Fork.le a b = true))

instance : DecidableRel (α := Diamond) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (Diamond.le a b = true))

/-- Extension necessity on a preorder is the box of its order. -/
theorem extBox_preorder_iff {α : Type*} [Preorder α] (P : α → Prop) (a : α) :
    extBox P a ↔ ∀ c, a ≤ c → P c :=
  ⟨fun h c hc => h c (homOfLE hc), fun h c f => h c (leOfHom f)⟩

theorem extDiamond_preorder_iff {α : Type*} [Preorder α] (P : α → Prop) (a : α) :
    extDiamond P a ↔ ∃ c, a ≤ c ∧ P c :=
  ⟨fun ⟨c, f, hc⟩ => ⟨c, leOfHom f, hc⟩, fun ⟨c, hac, hc⟩ => ⟨c, homOfLE hac, hc⟩⟩

/-- `.2` fails on the fork. -/
theorem fork_not_dot2 :
    ¬ (extDiamond (extBox (fun x : Fork => x = .left)) Fork.root →
        extBox (extDiamond (fun x : Fork => x = .left)) Fork.root) := by
  intro h
  have premise : extDiamond (extBox (fun x : Fork => x = .left)) Fork.root := by
    refine (extDiamond_preorder_iff _ _).2 ⟨.left, by decide, ?_⟩
    refine (extBox_preorder_iff _ _).2 fun c hc => ?_
    revert hc
    cases c <;> decide
  have := (extBox_preorder_iff _ _).1 (h premise) .right (by decide)
  obtain ⟨c, hc, hPc⟩ := (extDiamond_preorder_iff _ _).1 this
  revert hc hPc
  cases c <;> decide

/-- `.3` fails on the fork. -/
theorem fork_not_dot3 :
    ¬ (extBox (fun c => extBox (fun x : Fork => x = .left) c → c = .right) Fork.root ∨
        extBox (fun c => extBox (fun x : Fork => x = .right) c → c = .left) Fork.root) := by
  rintro (h | h)
  · have := (extBox_preorder_iff _ _).1 h .left (by decide)
      ((extBox_preorder_iff _ _).2 fun c hc => by revert hc; cases c <;> decide)
    exact absurd this (by decide)
  · have := (extBox_preorder_iff _ _).1 h .right (by decide)
      ((extBox_preorder_iff _ _).2 fun c hc => by revert hc; cases c <;> decide)
    exact absurd this (by decide)

/-- The diamond is directed, so `.2` holds on it. -/
theorem diamond_directed : Directed Diamond := by
  intro b c d f g
  have hc := leOfHom f
  have hd := leOfHom g
  refine ⟨.top, ⟨homOfLE ?_⟩, ⟨homOfLE ?_⟩⟩
  · revert hc
    cases b <;> cases c <;> decide
  · revert hd
    cases b <;> cases d <;> decide

theorem diamond_dot2 (P : Diamond → Prop) (b : Diamond) :
    extDiamond (extBox P) b → extBox (extDiamond P) b :=
  extBox_dot2 diamond_directed

/-- `.3` fails on the diamond. -/
theorem diamond_not_dot3 :
    ¬ (extBox (fun c => extBox (fun x : Diamond => x = .left ∨ x = .top) c →
            c = .right ∨ c = .top) Diamond.root ∨
        extBox (fun c => extBox (fun x : Diamond => x = .right ∨ x = .top) c →
            c = .left ∨ c = .top) Diamond.root) := by
  rintro (h | h)
  · have := (extBox_preorder_iff _ _).1 h .left (by decide)
      ((extBox_preorder_iff _ _).2 fun c hc => by revert hc; cases c <;> decide)
    exact absurd this (by decide)
  · have := (extBox_preorder_iff _ _).1 h .right (by decide)
      ((extBox_preorder_iff _ _).2 fun c hc => by revert hc; cases c <;> decide)
    exact absurd this (by decide)

/-! ## The source worlds -/

section Sources

open Sources

variable {Src : Type} [DecidableEq Src]

/-- The source worlds are directed: two extensions meet in their union. -/
theorem sources_directed : Directed (Finset Src) := by
  intro b c d _ _
  exact ⟨c ∪ d, ⟨homOfLE Finset.subset_union_left⟩, ⟨homOfLE Finset.subset_union_right⟩⟩

omit [DecidableEq Src] in
/-- With two sources, `.3` fails at the world without sources. -/
theorem sources_not_dot3 (a b : Src) (hab : a ≠ b) :
    ¬ (extBox (fun W => extBox (fun V : Finset Src => a ∈ V) W → b ∈ W) (∅ : Finset Src) ∨
        extBox (fun W => extBox (fun V : Finset Src => b ∈ V) W → a ∈ W) (∅ : Finset Src)) := by
  rintro (h | h)
  · have := (extBox_preorder_iff _ _).1 h {a} (Finset.empty_subset _)
      ((extBox_preorder_iff _ _).2 fun V hV => hV (Finset.mem_singleton_self a))
    exact hab (Finset.mem_singleton.mp this).symm
  · have := (extBox_preorder_iff _ _).1 h {b} (Finset.empty_subset _)
      ((extBox_preorder_iff _ _).2 fun V hV => hV (Finset.mem_singleton_self b))
    exact hab (Finset.mem_singleton.mp this)

/-- Epistemic access at a world: equal profiles there. -/
def Epistemic (W : Finset Src) (m m' : Records Src) : Prop := answer W m = answer W m'

/-- Operational reachability: revision by further records. -/
def Reachable (m m' : Records Src) : Prop := ∃ r : Records Src, m' = m + r

theorem epistemic_symmetric (W : Finset Src) {m m' : Records Src} (h : Epistemic W m m') :
    Epistemic W m' m := h.symm

/-- Epistemic access shrinks along extension: a finer world distinguishes more. -/
theorem epistemic_antitone {W W' : Finset Src} (h : W ⊆ W') {m m' : Records Src}
    (access : Epistemic W' m m') : Epistemic W m m' := by
  unfold Epistemic at *
  rw [← answer_restrict (homOfLE h) m, ← answer_restrict (homOfLE h) m', access]

omit [DecidableEq Src] in
/-- Reachability is not symmetric. -/
theorem reachability_not_symmetric (a : Src) :
    Reachable (0 : Records Src) {(a, true)} ∧ ¬ Reachable ({(a, true)} : Records Src) 0 := by
  refine ⟨⟨{(a, true)}, (zero_add _).symm⟩, ?_⟩
  rintro ⟨r, hr⟩
  have := congrArg Multiset.card hr
  simp at this

/-- Epistemic access does not give reachability. -/
theorem epistemic_not_reachable (a b : Src) (hab : a ≠ b) :
    Epistemic ∅ (stateAB a b) (stateBA a b) ∧ ¬ Reachable (stateAB a b) (stateBA a b) := by
  refine ⟨(swapped_profiles a b hab).1, ?_⟩
  rintro ⟨r, hr⟩
  have card := congrArg Multiset.card hr
  simp [stateAB, stateBA] at card
  subst card
  simp only [add_zero] at hr
  have := congrArg (fun m : Records Src => m.count (a, true)) hr
  simp only [(count_a_true a b hab).1, (count_a_true a b hab).2] at this
  exact absurd this (by decide)

/-- Reachability does not give epistemic access. -/
theorem reachable_not_epistemic (a : Src) :
    Reachable (0 : Records Src) {(a, true)} ∧ ¬ Epistemic ∅ (0 : Records Src) {(a, true)} := by
  refine ⟨⟨{(a, true)}, (zero_add _).symm⟩, fun h => ?_⟩
  have := congrFun h (.aggregate true)
  change ((0 : Records Src).filter (fun r => r.2 = true)).card =
    (({(a, true)} : Records Src).filter (fun r => r.2 = true)).card at this
  simp [Multiset.filter_singleton] at this

end Sources

end Mettapedia.Logic.WorldModel.Indexed.Modal
