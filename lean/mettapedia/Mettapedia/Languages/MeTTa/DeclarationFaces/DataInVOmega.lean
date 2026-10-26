import Mettapedia.Languages.MeTTa.DeclarationFaces.Faces
import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.Logic.Encodable.Basic

/-!
# Finite data lives in V_ω

Constructor data of an admitted declaration is finite trees, and its natural home as a set is the
hereditarily finite sets, `V_ω`. `code` sends a term to a ZF set: a symbol to the von Neumann
ordinal of its code, an application to the Kuratowski pair of its head and the list of its arguments.

* **Codes are injective on closed terms** (`code_injective`): two closed terms with one code are
  equal; constructors are injective with disjoint images as sets, so the encoding reads data as sets
  with no confusion. Variables, which are not data, are all coded by the empty set.
* **Codes are hereditarily finite** (`code_mem_omega`): every code lies in `V_ω`, the hereditarily
  finite sets, which the set lane of the tree identifies with the sets of its hereditary set terms
  (`OSLF.NativeTypes.GeneratedLogic.SetMembershipHFUniverse.isHFSet_iff_mem_vonNeumann`).

So the set a sort denotes (`Signature.Denotes`) is read as a subset of `V_ω` (`denotesSet`), and the
model of a defined function as a function between such subsets.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.DeclarationFaces

open Tm

variable {S : Type} [Encodable S]

/-- The von Neumann ordinal of a natural number, as a ZF set. -/
noncomputable def natSet (n : ℕ) : ZFSet.{0} := ZFSet.vonNeumann (n : Ordinal.{0})

theorem natSet_injective : Function.Injective natSet := by
  intro n m h
  have := ZFSet.vonNeumann_injective h
  exact_mod_cast this

mutual
/-- **The set of a term**: a variable by its name's code, a symbol applied to arguments as the pair
of the symbol's code and the arguments. -/
noncomputable def code : Tm S → ZFSet.{0}
  | .var _ => ∅
  | .app f args => ZFSet.pair (natSet (Encodable.encode f)) (codeList args)
/-- The set of a list of terms: nested pairs ending in the empty set. -/
noncomputable def codeList : List (Tm S) → ZFSet.{0}
  | [] => ∅
  | a :: as => ZFSet.pair (code a) (codeList as)
end

theorem pair_ne_empty (a b : ZFSet.{0}) : ZFSet.pair a b ≠ ∅ := by
  intro h
  have : ({a} : ZFSet.{0}) ∈ ZFSet.pair a b := by simp [ZFSet.pair]
  rw [h] at this
  exact ZFSet.notMem_empty _ this

omit [Encodable S] in
theorem closed_args {f : S} {args : List (Tm S)} (closed : (Tm.app f args).vars = []) :
    ∀ a ∈ args, a.vars = [] := by
  intro a ha
  simp only [vars_app, List.flatMap_eq_nil_iff] at closed
  exact closed a ha

mutual
/-- **Codes of closed terms are injective.** -/
theorem code_injective_aux : ∀ s t : Tm S, s.vars = [] → t.vars = [] → code s = code t → s = t
  | .var x, _, hs, _, _ => by simp at hs
  | .app f as, .var y, _, ht, _ => by simp at ht
  | .app f as, .app g bs, hs, ht, h => by
      simp only [code] at h
      obtain ⟨h₁, h₂⟩ := ZFSet.pair_injective h
      have hf : f = g := Encodable.encode_injective (natSet_injective h₁)
      rw [hf, codeList_injective_aux as bs (closed_args hs) (closed_args ht) h₂]
theorem codeList_injective_aux : ∀ as bs : List (Tm S), (∀ a ∈ as, a.vars = []) →
    (∀ b ∈ bs, b.vars = []) → codeList as = codeList bs → as = bs
  | [], [], _, _, _ => rfl
  | [], b :: bs, _, _, h => by simp only [codeList] at h; exact absurd h.symm (pair_ne_empty _ _)
  | a :: as, [], _, _, h => by simp only [codeList] at h; exact absurd h (pair_ne_empty _ _)
  | a :: as, b :: bs, ha, hb, h => by
      simp only [codeList] at h
      obtain ⟨h₁, h₂⟩ := ZFSet.pair_injective h
      rw [code_injective_aux a b (ha a List.mem_cons_self) (hb b List.mem_cons_self) h₁,
        codeList_injective_aux as bs (fun c hc => ha c (List.mem_cons_of_mem a hc))
          (fun c hc => hb c (List.mem_cons_of_mem b hc)) h₂]
end

/-- **Codes are injective on closed terms**: no confusion. -/
theorem code_injective {s t : Tm S} (hs : s.Closed) (ht : t.Closed) (h : code s = code t) : s = t :=
  code_injective_aux s t hs ht h

/-! ## Hereditary finiteness -/

/-- Membership in a finite stage. -/
def InStage (x : ZFSet.{0}) : Prop := ∃ n : ℕ, x ∈ ZFSet.vonNeumann (n : Ordinal.{0})

theorem vonNeumann_mono {n m : ℕ} (le : n ≤ m) :
    ZFSet.vonNeumann (n : Ordinal.{0}) ⊆ ZFSet.vonNeumann (m : Ordinal.{0}) := by
  intro x hx
  rw [ZFSet.mem_vonNeumann] at hx ⊢
  exact lt_of_lt_of_le hx (by exact_mod_cast le)

theorem InStage.mono {x : ZFSet.{0}} {n m : ℕ} (hx : x ∈ ZFSet.vonNeumann (n : Ordinal.{0}))
    (le : n ≤ m) : x ∈ ZFSet.vonNeumann (m : Ordinal.{0}) :=
  vonNeumann_mono le hx

/-- A set of two members of a finite stage is in the next stage. -/
theorem pairSet_stage {a b : ZFSet.{0}} {n : ℕ} (ha : a ∈ ZFSet.vonNeumann (n : Ordinal.{0}))
    (hb : b ∈ ZFSet.vonNeumann (n : Ordinal.{0})) :
    ({a, b} : ZFSet.{0}) ∈ ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{0}) := by
  rw [ZFSet.mem_vonNeumann']
  refine ⟨n, by exact_mod_cast Nat.lt_succ_self n, fun x hx => ?_⟩
  simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

theorem singleton_stage {a : ZFSet.{0}} {n : ℕ} (ha : a ∈ ZFSet.vonNeumann (n : Ordinal.{0})) :
    ({a} : ZFSet.{0}) ∈ ZFSet.vonNeumann ((n + 1 : ℕ) : Ordinal.{0}) := by
  rw [ZFSet.mem_vonNeumann']
  refine ⟨n, by exact_mod_cast Nat.lt_succ_self n, fun x hx => ?_⟩
  simp only [ZFSet.mem_singleton] at hx
  rw [hx]; exact ha

theorem pair_stage {a b : ZFSet.{0}} (ha : InStage a) (hb : InStage b) : InStage (ZFSet.pair a b) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  let k := max n m
  have ha' := InStage.mono hn (Nat.le_max_left n m)
  have hb' := InStage.mono hm (Nat.le_max_right n m)
  exact ⟨k + 2, pairSet_stage (singleton_stage ha') (pairSet_stage ha' hb')⟩

theorem natSet_stage (n : ℕ) : InStage (natSet n) :=
  ⟨n + 1, by
    rw [natSet, ZFSet.vonNeumann_mem_vonNeumann_iff]
    exact_mod_cast Nat.lt_succ_self n⟩

mutual
theorem code_stage : ∀ t : Tm S, InStage (code t)
  | .var x => ⟨1, by simp only [code]; rw [ZFSet.mem_vonNeumann]; simp⟩
  | .app f args => by simp only [code]; exact pair_stage (natSet_stage _) (codeList_stage args)
theorem codeList_stage : ∀ args : List (Tm S), InStage (codeList args)
  | [] => ⟨1, by simp only [codeList]; rw [ZFSet.mem_vonNeumann]; simp⟩
  | a :: as => by simp only [codeList]; exact pair_stage (code_stage a) (codeList_stage as)
end

/-- **Every code is a hereditarily finite set**: it lies in `V_ω`. -/
theorem code_mem_omega (t : Tm S) : code t ∈ ZFSet.vonNeumann Ordinal.omega0 := by
  obtain ⟨n, hn⟩ := code_stage t
  rw [ZFSet.mem_vonNeumann] at hn ⊢
  exact lt_of_lt_of_le hn (le_of_lt (Ordinal.natCast_lt_omega0 n))

/-- **The set a sort denotes, read in `V_ω`.** -/
def denotesSet [DecidableEq S] (sig : Signature S) (τ : Sort') : Set ZFSet.{0} :=
  code '' sig.Denotes τ

theorem denotesSet_subset_omega [DecidableEq S] (sig : Signature S) (τ : Sort') :
    denotesSet sig τ ⊆ {x | x ∈ ZFSet.vonNeumann Ordinal.omega0} := by
  rintro _ ⟨v, _, rfl⟩
  exact code_mem_omega v

/-- **Membership in the coded set is membership in the sort's set**: no confusion. -/
theorem code_mem_denotesSet_iff [DecidableEq S] (sig : Signature S) (τ : Sort') {v : Tm S}
    (closed : v.Closed) : code v ∈ denotesSet sig τ ↔ v ∈ sig.Denotes τ := by
  constructor
  · rintro ⟨w, hw, same⟩
    rwa [← code_injective (HasSort.closed_of_empty hw.2) closed same]
  · intro hv
    exact ⟨v, hv, rfl⟩

end Mettapedia.Languages.MeTTa.DeclarationFaces
