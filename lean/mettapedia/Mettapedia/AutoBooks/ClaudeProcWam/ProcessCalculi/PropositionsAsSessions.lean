/-
# Propositions as Sessions

Formalization of Wadler's (2012) correspondence between propositions
and sessions, building on Caires-Pfenning (2010).

## Key Correspondence

| Linear Logic      | Session Type     | Process           |
|-------------------|------------------|-------------------|
| A ⊗ B             | A ⊗ B            | x[y].(P | Q)      |
| A ⅋ B             | A ⅋ B            | x(y).P            |
| A & B             | A & B            | x.case(P, Q)      |
| A ⊕ B             | A ⊕ B            | x.inl; P          |
| !A                | !A               | !x(y).P           |
| ?A                | ?A               | ?x[y].P           |
| 1                 | end              | x[].0             |
| ⊥                 | end⊥             | x().P             |

## Checked fragments and open obligations

The retained material covers formula duality, process substitution, structural
rules, and equivalence with the depth-indexed typing relation. The legacy
preservation, progress, and context-invariant attempts depended on admitted
proofs and are recorded as open claims in the integration research-status
ledger. They are not exported as proved theorems.

The current typing relation omits freshness and context-disjointness premises;
its top rule permits an arbitrary process. The counterexamples at the end
show that it forces neither context linearity nor coverage of free channels.
A complete CP metatheory requires an appropriately constrained relation.

## References

- Wadler (2012): Propositions as Sessions
- Caires & Pfenning (2010): Session Types as Intuitionistic Linear Propositions
-/

import Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi.SessionTypes

namespace Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi

open SessionType

/-! ## Classical Linear Logic (CLL) Propositions

Following Wadler, we use classical linear logic for symmetric duality.
-/

/-- Classical linear logic propositions -/
inductive CLLProp where
  /-- Atomic proposition -/
  | atom : String → CLLProp
  /-- Dual of atomic -/
  | atomDual : String → CLLProp
  /-- Tensor: A ⊗ B -/
  | tensor : CLLProp → CLLProp → CLLProp
  /-- Par: A ⅋ B -/
  | par : CLLProp → CLLProp → CLLProp
  /-- With: A & B -/
  | addConj : CLLProp → CLLProp → CLLProp
  /-- Plus: A ⊕ B -/
  | addDisj : CLLProp → CLLProp → CLLProp
  /-- One: 1 -/
  | one : CLLProp
  /-- Bottom: ⊥ -/
  | bot : CLLProp
  /-- Top: ⊤ -/
  | top : CLLProp
  /-- Zero: 0 -/
  | zero : CLLProp
  /-- Of course: !A -/
  | ofCourse : CLLProp → CLLProp
  /-- Why not: ?A -/
  | whyNot : CLLProp → CLLProp
  deriving DecidableEq, Repr, Inhabited

namespace CLLProp

/-- Linear negation (duality) -/
def dual : CLLProp → CLLProp
  | .atom x => .atomDual x
  | .atomDual x => .atom x
  | .tensor a b => .par a.dual b.dual
  | .par a b => .tensor a.dual b.dual
  | .addConj a b => .addDisj a.dual b.dual
  | .addDisj a b => .addConj a.dual b.dual
  | .one => .bot
  | .bot => .one
  | .top => .zero
  | .zero => .top
  | .ofCourse a => .whyNot a.dual
  | .whyNot a => .ofCourse a.dual

/-- Duality is involutive -/
theorem dual_dual (a : CLLProp) : a.dual.dual = a := by
  induction a with
  | atom _ => rfl
  | atomDual _ => rfl
  | one => rfl
  | bot => rfl
  | top => rfl
  | zero => rfl
  | tensor a b iha ihb => simp only [dual, iha, ihb]
  | par a b iha ihb => simp only [dual, iha, ihb]
  | addConj a b iha ihb => simp only [dual, iha, ihb]
  | addDisj a b iha ihb => simp only [dual, iha, ihb]
  | ofCourse a ih => simp only [dual, ih]
  | whyNot a ih => simp only [dual, ih]

-- Retain the established qualified name of this legacy declaration.
set_option linter.dupNamespace false in
/-- No CLLProp is self-dual. Each constructor maps to a different constructor under dual. -/
theorem CLLProp.dual_ne_self (a : CLLProp) : a ≠ a.dual := by
  cases a with
  | atom _ => exact fun h => nomatch h
  | atomDual _ => exact fun h => nomatch h
  | tensor _ _ => exact fun h => nomatch h
  | par _ _ => exact fun h => nomatch h
  | addConj _ _ => exact fun h => nomatch h
  | addDisj _ _ => exact fun h => nomatch h
  | one => exact fun h => nomatch h
  | bot => exact fun h => nomatch h
  | top => exact fun h => nomatch h
  | zero => exact fun h => nomatch h
  | ofCourse _ => exact fun h => nomatch h
  | whyNot _ => exact fun h => nomatch h

instance : ToString CLLProp where
  toString p := go p
where
  go : CLLProp → String
    | .atom x => x
    | .atomDual x => s!"{x}⊥"
    | .tensor a b => s!"({go a} ⊗ {go b})"
    | .par a b => s!"({go a} ⅋ {go b})"
    | .addConj a b => s!"({go a} & {go b})"
    | .addDisj a b => s!"({go a} ⊕ {go b})"
    | .one => "1"
    | .bot => "⊥"
    | .top => "⊤"
    | .zero => "0"
    | .ofCourse a => s!"!{go a}"
    | .whyNot a => s!"?{go a}"

end CLLProp

/-! ## Typing Contexts

Linear contexts where each proposition is used exactly once.
Contexts are multisets of (channel, proposition) pairs.
-/

/-- Channel name -/
abbrev Chan := String

/-- A typing assignment: channel has type A -/
structure TypeAssign where
  chan : Chan
  prop : CLLProp
  deriving DecidableEq, Repr

/-- Typing context (linear, so multiset semantics) -/
abbrev Context := List TypeAssign

/-- Empty context -/
def Context.empty : Context := []

/-- Singleton context -/
def Context.singleton (x : Chan) (a : CLLProp) : Context := [{ chan := x, prop := a }]

/-- Context union (for tensor rule) -/
def Context.union (Γ Δ : Context) : Context := Γ ++ Δ

/-- A context is linear if each channel appears at most once -/
def Context.linear (Γ : Context) : Prop :=
  ∀ i j : Fin Γ.length, Γ[i].chan = Γ[j].chan → i = j

/-- Get all channels in a context -/
def Context.chans (Γ : Context) : List Chan := Γ.map (·.chan)

/-- Channel not in context -/
def Context.notMem (c : Chan) (Γ : Context) : Prop := c ∉ Γ.chans

/-- Two contexts are disjoint (no shared channels) -/
def Context.disjoint (Γ Δ : Context) : Prop :=
  ∀ c ∈ Γ.chans, c ∉ Δ.chans

/-- In a linear context, if a channel appears at position n, it doesn't appear before n -/
theorem Context.linear_no_dup_prefix (Γ : Context) (hlin : Γ.linear) (n : Fin Γ.length)
    (i : Fin Γ.length) (hi : i.val < n.val) : Γ[i].chan ≠ Γ[n].chan := by
  intro heq
  have := hlin i n heq
  omega

/-- Channel at end of context is not in the prefix -/
theorem Context.end_not_in_prefix (Γ : Context) (ta : TypeAssign) (hlin : (Γ ++ [ta]).linear) :
    ta.chan ∉ Γ.chans := by
  intro hmem
  simp only [Context.chans, List.mem_map] at hmem
  obtain ⟨ta', hta'Γ, hchan⟩ := hmem
  -- ta' ∈ Γ with ta'.chan = ta.chan
  -- In the linear context Γ ++ [ta], ta appears at position |Γ|
  -- ta' appears at some position i < |Γ|
  -- They have the same channel, contradicting linearity
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hta'Γ
  have hn : Γ.length < (Γ ++ [ta]).length := by simp
  have hilt : i < (Γ ++ [ta]).length := Nat.lt_of_lt_of_le hi (by simp)
  let fi : Fin (Γ ++ [ta]).length := ⟨i, hilt⟩
  let fn : Fin (Γ ++ [ta]).length := ⟨Γ.length, hn⟩
  have hget_i : (Γ ++ [ta]).get fi = Γ[i] := by simp [fi, List.getElem_append_left hi]
  have hget_n : (Γ ++ [ta]).get fn = ta := by simp [fn]
  have heq' : ((Γ ++ [ta]).get fi).chan = ((Γ ++ [ta]).get fn).chan := by
    simp only [hget_i, hget_n, hget, hchan]
  have hfin_eq := hlin fi fn heq'
  simp only [fi, fn, Fin.mk.injEq] at hfin_eq
  omega

/-! ## Processes (π-calculus with Sessions)

Based on Wadler's CP calculus.
-/

/-- Process terms -/
inductive CPProc where
  /-- Terminated process -/
  | nil : CPProc
  /-- Parallel composition: P | Q -/
  | par : CPProc → CPProc → CPProc
  /-- Output on x, bind y, continue as P | Q -/
  | out : Chan → Chan → CPProc → CPProc → CPProc
  /-- Input on x, bind y, continue as P -/
  | inp : Chan → Chan → CPProc → CPProc
  /-- Left selection on x, continue as P -/
  | inl : Chan → CPProc → CPProc
  /-- Right selection on x, continue as P -/
  | inr : Chan → CPProc → CPProc
  /-- Case on x, branches P and Q -/
  | case : Chan → CPProc → CPProc → CPProc
  /-- Empty output on x (for 1) -/
  | emptyOut : Chan → CPProc
  /-- Empty input on x, continue as P (for ⊥) -/
  | emptyInp : Chan → CPProc → CPProc
  /-- Server accept on x, bind y, continue as P -/
  | accept : Chan → Chan → CPProc → CPProc
  /-- Client request on x, bind y, continue as P -/
  | request : Chan → Chan → CPProc → CPProc
  /-- Link two channels -/
  | link : Chan → Chan → CPProc
  /-- Channel restriction (new channel) -/
  | nu : Chan → CLLProp → CPProc → CPProc
  deriving Repr, Inhabited

instance : ToString CPProc where
  toString p := go p
where
  go : CPProc → String
    | .nil => "0"
    | .par p q => s!"({go p} | {go q})"
    | .out x y p q => s!"{x}[{y}].({go p} | {go q})"
    | .inp x y p => s!"{x}({y}).{go p}"
    | .inl x p => s!"{x}.inl;{go p}"
    | .inr x p => s!"{x}.inr;{go p}"
    | .case x p q => s!"{x}.case({go p}, {go q})"
    | .emptyOut x => s!"{x}[]"
    | .emptyInp x p => s!"{x}().{go p}"
    | .accept x y p => s!"!{x}({y}).{go p}"
    | .request x y p => s!"?{x}[{y}].{go p}"
    | .link x w => s!"{x}↔{w}"
    | .nu x a p => s!"(ν{x}:{a}){go p}"

/-- Channel substitution in processes: P[y/z] replaces z with y -/
def CPProc.subst (p : CPProc) (y z : Chan) : CPProc :=
  let s := fun c => if c == z then y else c
  match p with
  | .nil => .nil
  | .par p1 p2 => .par (p1.subst y z) (p2.subst y z)
  | .out x w p1 p2 =>
    if w == z then .out (s x) w p1 (p2.subst y z)  -- w binds z in p1
    else .out (s x) (s w) (p1.subst y z) (p2.subst y z)
  | .inp x w p1 =>
    if w == z then p  -- z is bound, don't substitute in body
    else .inp (s x) w (p1.subst y z)
  | .inl x p1 => .inl (s x) (p1.subst y z)
  | .inr x p1 => .inr (s x) (p1.subst y z)
  | .case x p1 p2 => .case (s x) (p1.subst y z) (p2.subst y z)
  | .emptyOut x => .emptyOut (s x)
  | .emptyInp x p1 => .emptyInp (s x) (p1.subst y z)
  | .accept x w p1 =>
    if w == z then .accept (s x) w p1  -- z is bound
    else .accept (s x) w (p1.subst y z)
  | .request x w p1 =>
    if w == z then .request (s x) w p1  -- z is bound
    else .request (s x) w (p1.subst y z)
  | .link x w => .link (s x) (s w)
  | .nu x a p1 =>
    if x == z then p  -- z is bound by ν, don't substitute
    else .nu x a (p1.subst y z)

/-- Free channels in a process (channels mentioned that aren't bound).
    In tensor output `x[w].(P|Q)`, the channel `w` is bound (sent to partner)
    and used in P, so it's filtered from P's free channels. -/
def CPProc.freeChans : CPProc → List Chan
  | .nil => []
  | .par p1 p2 => p1.freeChans ++ p2.freeChans
  | .out x w p1 p2 => [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
  | .inp x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .inl x p1 => [x] ++ p1.freeChans
  | .inr x p1 => [x] ++ p1.freeChans
  | .case x p1 p2 => [x] ++ p1.freeChans ++ p2.freeChans
  | .emptyOut x => [x]
  | .emptyInp x p1 => [x] ++ p1.freeChans
  | .accept x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .request x w p1 => [x] ++ (p1.freeChans.filter (· != w))
  | .link x w => [x, w]
  | .nu x _ p1 => p1.freeChans.filter (· != x)

/-- Helper: if x == y then y else x = x -/
private theorem beq_ite_self (x y : Chan) : (if x == y then y else x) = x := by
  by_cases h : x = y
  · simp [h]
  · simp [beq_eq_false_iff_ne.mpr h]

/-- Substituting a channel for itself has no effect -/
theorem CPProc.subst_self (p : CPProc) (y : Chan) : p.subst y y = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 => simp only [subst, ih1, ih2]
  | out x w p1 p2 ih1 ih2 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self, ih2]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1, ih2]
  | inp x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | inl x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | inr x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | case x p1 p2 ih1 ih2 => simp only [subst, beq_ite_self, ih1, ih2]
  | emptyOut x => simp only [subst, beq_ite_self]
  | emptyInp x p1 ih1 => simp only [subst, beq_ite_self, ih1]
  | accept x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | request x w p1 ih1 =>
    simp only [subst]
    by_cases hw : w = y
    · simp only [hw, beq_self_eq_true, ↓reduceIte, beq_ite_self]
    · simp only [beq_eq_false_iff_ne.mpr hw, Bool.false_eq_true, ↓reduceIte, beq_ite_self, ih1]
  | link x w => simp only [subst, beq_ite_self]
  | nu x a p1 ih1 =>
    simp only [subst]
    by_cases hx : x = y
    · simp only [hx, beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, ↓reduceIte, ih1]

/-- Substituting a channel not free in the process has no effect -/
theorem CPProc.subst_not_free (p : CPProc) (y z : Chan) (h : z ∉ p.freeChans) :
    p.subst y z = p := by
  induction p with
  | nil => rfl
  | par p1 p2 ih1 ih2 =>
    simp only [freeChans, List.mem_append, not_or] at h
    simp only [subst, ih1 h.1, ih2 h.2]
  | out x w p1 p2 ih1 ih2 =>
    -- freeChans: [x] ++ (p1.freeChans.filter (· != w)) ++ p2.freeChans
    -- subst: if w == z then .out (s x) w p1 (p2.subst y z) else .out (s x) (s w) ...
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    -- h.1.1 : z ≠ x, h.1.2 : z ∈ p1.freeChans → z = w, h.2 : z ∉ p2.freeChans
    unfold subst
    by_cases hwz : w = z
    · -- w = z: binding shadows z in p1, only substitute in p2
      have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwz, beq_self_eq_true, ↓reduceIte, hxz, Bool.false_eq_true, ih2 h2]
    · have hzx : z ≠ x := h.1.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      -- h.1.2 : z ∈ p1.freeChans → ¬z ≠ w (i.e., → z = w by double negation)
      have h1 : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.1.2 hmem)).symm
      have h2 : z ∉ p2.freeChans := h.2
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 h1, ih2 h2]
  | inp x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · simp only [hwz, beq_self_eq_true, ↓reduceIte]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | inl x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | inr x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | case x p1 p2 ih1 ih2 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    have h1 : z ∉ p1.freeChans := h.1.2
    have h2 : z ∉ p2.freeChans := h.2
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h1, ih2 h2]
  | emptyOut x =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h heq.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte]
  | emptyInp x p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hzx : z ≠ x := h.1
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
    simp only [subst, hxz, Bool.false_eq_true, ↓reduceIte, ih1 h.2]
  | accept x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | request x w p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
               List.mem_filter, not_or, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hwz : w = z
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      simp only [hwz, beq_self_eq_true, hxz, Bool.false_eq_true, if_true, if_false]
    · have hzx : z ≠ x := h.1
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr hzx.symm
      have hwne : w ≠ z := fun heq => hwz heq
      have hwzf : (w == z) = false := beq_eq_false_iff_ne.mpr hwne
      have hfree : z ∉ p1.freeChans := fun hmem =>
        hwz (Decidable.not_not.mp (h.2 hmem)).symm
      simp only [hwzf, Bool.false_eq_true, ↓reduceIte, hxz, ih1 hfree]
  | link x w =>
    unfold freeChans at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.1 heq.symm
    have hwz : (w == z) = false := beq_eq_false_iff_ne.mpr fun heq => h.2 heq.symm
    simp only [subst, hxz, hwz, Bool.false_eq_true, ↓reduceIte]
  | nu x a p1 ih1 =>
    unfold freeChans at h
    simp only [List.mem_filter, not_and, bne_iff_ne] at h
    unfold subst
    by_cases hxz : x = z
    · simp only [hxz, beq_self_eq_true, ↓reduceIte]
    · have hfree : z ∉ p1.freeChans := fun hmem => h hmem fun heq => hxz heq.symm
      simp only [beq_eq_false_iff_ne.mpr hxz, Bool.false_eq_true, ↓reduceIte, ih1 hfree]

/-! ## Typing Rules

These correspond to linear logic proof rules.
-/

/-- Helper to create type assignment -/
def mkAssign (x : Chan) (a : CLLProp) : TypeAssign := { chan := x, prop := a }

/-- Well-typedness judgment: Γ ⊢ P -/
inductive CPTyped : Context → CPProc → Prop where
  /-- Axiom/Link: x:A, w:A⊥ ⊢ x↔w -/
  | ax (x w : Chan) (a : CLLProp) :
      CPTyped [mkAssign x a, mkAssign w a.dual] (.link x w)

  /-- Cut: If Γ,x:A ⊢ P and Δ,x:A⊥ ⊢ Q then Γ,Δ ⊢ (νx:A)(P | Q) -/
  | cut (Γ Δ : Context) (x : Chan) (a : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x a.dual]) q) :
      CPTyped (Γ ++ Δ) (.nu x a (.par p q))

  /-- ⊗R: If Γ,y:A ⊢ P and Δ,x:B ⊢ Q then Γ,Δ,x:A⊗B ⊢ x[y].(P|Q) -/
  | tensorR (Γ Δ : Context) (x y : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a]) p)
      (hq : CPTyped (Δ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ Δ ++ [mkAssign x (.tensor a b)]) (.out x y p q)

  /-- ⅋R: If Γ,y:A,x:B ⊢ P then Γ,x:A⅋B ⊢ x(y).P -/
  | parR (Γ : Context) (x y : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.par a b)]) (.inp x y p)

  /-- &R: If Γ,x:A ⊢ P and Γ,x:B ⊢ Q then Γ,x:A&B ⊢ x.case(P,Q) -/
  | addConjR (Γ : Context) (x : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p)
      (hq : CPTyped (Γ ++ [mkAssign x b]) q) :
      CPTyped (Γ ++ [mkAssign x (.addConj a b)]) (.case x p q)

  /-- ⊕R₁: If Γ,x:A ⊢ P then Γ,x:A⊕B ⊢ x.inl;P -/
  | addDisjR1 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x a]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inl x p)

  /-- ⊕R₂: If Γ,x:B ⊢ P then Γ,x:A⊕B ⊢ x.inr;P -/
  | addDisjR2 (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTyped (Γ ++ [mkAssign x b]) p) :
      CPTyped (Γ ++ [mkAssign x (.addDisj a b)]) (.inr x p)

  /-- 1R: x:1 ⊢ x[] -/
  | oneR (x : Chan) :
      CPTyped [mkAssign x .one] (.emptyOut x)

  /-- ⊥R: If Γ ⊢ P then Γ,x:⊥ ⊢ x().P -/
  | botR (Γ : Context) (x : Chan) (p : CPProc)
      (hp : CPTyped Γ p) :
      CPTyped (Γ ++ [mkAssign x .bot]) (.emptyInp x p)

  /-- ⊤R: Γ,x:⊤ ⊢ anything (unused premise) -/
  | topR (Γ : Context) (x : Chan) (p : CPProc) :
      CPTyped (Γ ++ [mkAssign x .top]) p

  /-- Mix: If Γ ⊢ P and Δ ⊢ Q then Γ,Δ ⊢ P | Q
      Parallel composition with disjoint contexts (mix rule). -/
  | mix (Γ Δ : Context) (p q : CPProc)
      (hp : CPTyped Γ p)
      (hq : CPTyped Δ q) :
      CPTyped (Γ ++ Δ) (.par p q)

/-! ### Depth-Indexed Typing for Strong Induction

We define a depth-indexed version of the typing judgment for strong induction proofs.
The depth bounds the height of the derivation tree. -/

/-- Depth-indexed typing: CPTypedD n Γ p means Γ ⊢ p is derivable in at most n steps -/
inductive CPTypedD : Nat → Context → CPProc → Prop where
  | ax (x w : Chan) (a : CLLProp) :
      CPTypedD 0 [mkAssign x a, mkAssign w a.dual] (.link x w)
  | cut (n m : Nat) (Γ Δ : Context) (x : Chan) (a : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p)
      (hq : CPTypedD m (Δ ++ [mkAssign x a.dual]) q) :
      CPTypedD (n + m + 1) (Γ ++ Δ) (.nu x a (.par p q))
  | tensorR (n m : Nat) (Γ Δ : Context) (x y : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign y a]) p)
      (hq : CPTypedD m (Δ ++ [mkAssign x b]) q) :
      CPTypedD (n + m + 1) (Γ ++ Δ ++ [mkAssign x (.tensor a b)]) (.out x y p q)
  | parR (n : Nat) (Γ : Context) (x y : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign y a, mkAssign x b]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.par a b)]) (.inp x y p)
  | addConjR (n m : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p q : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p)
      (hq : CPTypedD m (Γ ++ [mkAssign x b]) q) :
      CPTypedD (n + m + 1) (Γ ++ [mkAssign x (.addConj a b)]) (.case x p q)
  | addDisjR1 (n : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x a]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.addDisj a b)]) (.inl x p)
  | addDisjR2 (n : Nat) (Γ : Context) (x : Chan) (a b : CLLProp) (p : CPProc)
      (hp : CPTypedD n (Γ ++ [mkAssign x b]) p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x (.addDisj a b)]) (.inr x p)
  | oneR (x : Chan) :
      CPTypedD 0 [mkAssign x .one] (.emptyOut x)
  | botR (n : Nat) (Γ : Context) (x : Chan) (p : CPProc)
      (hp : CPTypedD n Γ p) :
      CPTypedD (n + 1) (Γ ++ [mkAssign x .bot]) (.emptyInp x p)
  | topR (Γ : Context) (x : Chan) (p : CPProc) :
      CPTypedD 0 (Γ ++ [mkAssign x .top]) p
  | mix (n m : Nat) (Γ Δ : Context) (p q : CPProc)
      (hp : CPTypedD n Γ p)
      (hq : CPTypedD m Δ q) :
      CPTypedD (n + m + 1) (Γ ++ Δ) (.par p q)

/-- Depth-indexed typing implies regular typing -/
theorem CPTypedD.toCPTyped : CPTypedD n Γ p → CPTyped Γ p := by
  intro h
  induction h with
  | ax x w a => exact CPTyped.ax x w a
  | cut _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.cut _ _ _ _ _ _ ihp ihq
  | tensorR _ _ _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.tensorR _ _ _ _ _ _ _ _ ihp ihq
  | parR _ _ _ _ _ _ _ _ ihp => exact CPTyped.parR _ _ _ _ _ _ ihp
  | addConjR _ _ _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.addConjR _ _ _ _ _ _ ihp ihq
  | addDisjR1 _ _ _ _ _ _ _ ihp => exact CPTyped.addDisjR1 _ _ _ _ _ ihp
  | addDisjR2 _ _ _ _ _ _ _ ihp => exact CPTyped.addDisjR2 _ _ _ _ _ ihp
  | oneR x => exact CPTyped.oneR x
  | botR _ _ _ _ _ ihp => exact CPTyped.botR _ _ _ ihp
  | topR Γ x p => exact CPTyped.topR Γ x p
  | mix _ _ _ _ _ _ _ _ ihp ihq => exact CPTyped.mix _ _ _ _ ihp ihq

/-- Regular typing implies depth-indexed typing for some depth -/
theorem CPTyped.toCPTypedD (h : CPTyped Γ p) : ∃ n, CPTypedD n Γ p := by
  induction h with
  | ax x w a => exact ⟨0, CPTypedD.ax x w a⟩
  | cut _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.cut n m _ _ _ _ _ _ hn hm⟩
  | tensorR _ _ _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.tensorR n m _ _ _ _ _ _ _ _ hn hm⟩
  | parR _ _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.parR n _ _ _ _ _ _ hn⟩
  | addConjR _ _ _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.addConjR n m _ _ _ _ _ _ hn hm⟩
  | addDisjR1 _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.addDisjR1 n _ _ _ _ _ hn⟩
  | addDisjR2 _ _ _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.addDisjR2 n _ _ _ _ _ hn⟩
  | oneR x => exact ⟨0, CPTypedD.oneR x⟩
  | botR _ _ _ _ ihp =>
    obtain ⟨n, hn⟩ := ihp
    exact ⟨n + 1, CPTypedD.botR n _ _ _ hn⟩
  | topR Γ x p => exact ⟨0, CPTypedD.topR Γ x p⟩
  | mix _ _ _ _ _ _ ihp ihq =>
    obtain ⟨n, hn⟩ := ihp
    obtain ⟨m, hm⟩ := ihq
    exact ⟨n + m + 1, CPTypedD.mix n m _ _ _ _ hn hm⟩

/-- Equivalence between depth-indexed and regular typing -/
theorem CPTyped_iff_CPTypedD : CPTyped Γ p ↔ ∃ n, CPTypedD n Γ p :=
  ⟨CPTyped.toCPTypedD, fun ⟨_, h⟩ => h.toCPTyped⟩

/- Unproved legacy claim: see the integration research-status ledger. -/

/-! ## Normal Forms

A process is in normal form if it cannot reduce further. In CP calculus,
normal forms are nil or parallel compositions of normal forms. -/

/-- Process normal form predicate. A process is a normal form if it is:
    - nil (terminated)
    - par of two normal forms (parallel threads both terminated) -/
def CPProc.isNormalForm : CPProc → Prop
  | .nil => True
  | .par p q => p.isNormalForm ∧ q.isNormalForm
  | _ => False

/-- nil is a normal form -/
theorem CPProc.nil_isNormalForm : CPProc.nil.isNormalForm := trivial

/-- par of normal forms is a normal form -/
theorem CPProc.par_isNormalForm (hp : p.isNormalForm) (hq : q.isNormalForm) :
    (CPProc.par p q).isNormalForm := ⟨hp, hq⟩

/-! ## Reduction (Communication)

Process reduction corresponds to cut elimination.
-/

/-- Structural congruence for processes -/
inductive CPCong : CPProc → CPProc → Prop where
  | refl (p : CPProc) : CPCong p p
  | symm (p q : CPProc) : CPCong p q → CPCong q p
  | trans (p q r : CPProc) : CPCong p q → CPCong q r → CPCong p r
  -- Scope extrusion rules would go here

/-- One-step reduction -/
inductive CPReduce : CPProc → CPProc → Prop where
  /-- β-tensor/par: (νx:A⊗B)(x[y].(P|Q) | x(z).R) → (νy:A)(P | R[y/z]) | Q
      Principal cut for tensor ⊗ and par ⅋. The tensor side sends channel y,
      the par side receives and binds z, which gets substituted by y. -/
  | beta_tensor_par (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.tensor a b)
          (.par (.out x y p q) (.inp x z r)))
        (.par (.nu y a (.par p (r.subst y z))) q)

  /-- β-par/tensor: symmetric case -/
  | beta_par_tensor (x y z : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.par a b)
          (.par (.inp x y p) (.out x z q r)))
        (.par (.nu y a (.par p (q.subst y z))) r)

  /-- β-addDisj-l/addConj: (νx:A⊕B)(x.inl;P | x.case(Q,R)) → (νx:A)(P | Q)
      The ⊕ side selects left, the & side provides the left branch. -/
  | beta_addDisj_l (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inl x p) (.case x q r)))
        (.nu x a (.par p q))

  /-- β-addDisj-r/addConj: (νx:A⊕B)(x.inr;P | x.case(Q,R)) → (νx:B)(P | R) -/
  | beta_addDisj_r (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addDisj a b)
          (.par (.inr x p) (.case x q r)))
        (.nu x b (.par p r))

  /-- β-addConj-l/addDisj: (νx:A&B)(x.case(P,Q) | x.inl;R) → (νx:A)(P | R)
      Symmetric case where conjunction is on the left. -/
  | beta_addConj_l (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addConj a b)
          (.par (.case x p q) (.inl x r)))
        (.nu x a (.par p r))

  /-- β-addConj-r/addDisj: (νx:A&B)(x.case(P,Q) | x.inr;R) → (νx:B)(Q | R)
      Symmetric case where conjunction is on the left, right branch selected. -/
  | beta_addConj_r (x : Chan) (a b : CLLProp) (p q r : CPProc) :
      CPReduce
        (.nu x (.addConj a b)
          (.par (.case x p q) (.inr x r)))
        (.nu x b (.par q r))

  /-- β-one/bot: (νx:1)(x[] | x().P) → P
      Unit/counit interaction. -/
  | beta_one_bot (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .one (.par (.emptyOut x) (.emptyInp x p)))
        p

  /-- β-bot/one: symmetric case -/
  | beta_bot_one (x : Chan) (p : CPProc) :
      CPReduce
        (.nu x .bot (.par (.emptyInp x p) (.emptyOut x)))
        p

  /-- Congruence: reduction under restriction -/
  | cong_nu (x : Chan) (a : CLLProp) (p p' : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.nu x a p) (.nu x a p')

  /-- Congruence: reduction in left of parallel -/
  | cong_par_l (p p' q : CPProc)
      (hred : CPReduce p p') :
      CPReduce (.par p q) (.par p' q)

  /-- Congruence: reduction in right of parallel -/
  | cong_par_r (p q q' : CPProc)
      (hred : CPReduce q q') :
      CPReduce (.par p q) (.par p q')

/-! ## Properties -/

/-! ### Inversion Lemmas

    These lemmas characterize the possible typing derivations for specific process forms.
    They are needed to handle dependent elimination in the principal cut cases. -/

/-- Inversion for .emptyOut: only oneR or topR can type it -/
lemma CPTyped.emptyOut_inv (Γ : Context) (x : Chan) (h : CPTyped Γ (.emptyOut x)) :
    (Γ = [mkAssign x .one]) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | oneR x' => left; rfl
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .emptyInp: only botR or topR can type it -/
lemma CPTyped.emptyInp_inv (Γ : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γ (.emptyInp x p)) :
    (∃ Δ, Γ = Δ ++ [mkAssign x .bot] ∧ CPTyped Δ p) ∨
    (∃ Γ' y, Γ = Γ' ++ [mkAssign y .top]) := by
  cases h with
  | botR Δ x' p' hp => left; exact ⟨Δ, rfl, hp⟩
  | topR Γ' y _ => right; exact ⟨Γ', y, rfl⟩

/-- Inversion for .out (tensor output): only tensorR or topR can type it -/
lemma CPTyped.out_inv (Γctx : Context) (x y : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.out x y p q)) :
    (∃ Γ Δ a b, Γctx = Γ ++ Δ ++ [mkAssign x (.tensor a b)] ∧
                CPTyped (Γ ++ [mkAssign y a]) p ∧
                CPTyped (Δ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | tensorR Γ Δ x' y' a b p' q' hp hq =>
    left; exact ⟨Γ, Δ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inp (par input): only parR or topR can type it -/
lemma CPTyped.inp_inv (Γctx : Context) (x y : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inp x y p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.par a b)] ∧
              CPTyped (Γ ++ [mkAssign y a, mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | parR Γ x' y' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .case (additive conjunction): only addConjR or topR can type it -/
lemma CPTyped.case_inv (Γctx : Context) (x : Chan) (p q : CPProc)
    (h : CPTyped Γctx (.case x p q)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addConj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p ∧
              CPTyped (Γ ++ [mkAssign x b]) q) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addConjR Γ x' a b p' q' hp hq => left; exact ⟨Γ, a, b, rfl, hp, hq⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inl (additive left): only addDisjR1 or topR can type it -/
lemma CPTyped.inl_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inl x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x a]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR1 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-- Inversion for .inr (additive right): only addDisjR2 or topR can type it -/
lemma CPTyped.inr_inv (Γctx : Context) (x : Chan) (p : CPProc)
    (h : CPTyped Γctx (.inr x p)) :
    (∃ Γ a b, Γctx = Γ ++ [mkAssign x (.addDisj a b)] ∧
              CPTyped (Γ ++ [mkAssign x b]) p) ∨
    (∃ Γ' z, Γctx = Γ' ++ [mkAssign z .top]) := by
  cases h with
  | addDisjR2 Γ x' a b p' hp => left; exact ⟨Γ, a, b, rfl, hp⟩
  | topR Γ' z _ => right; exact ⟨Γ', z, rfl⟩

/-! ### Impossibility Lemmas for Certain Contexts

    Key insight: The only singleton contexts directly derivable (without cut/mix) are:
    - [x:1] via oneR
    - [x:⊤] via topR (with Γ = [])

    For empty context [], we'd need to cut matching singletons [x:a] and [x:a.dual].
    But 1.dual = ⊥ and ⊤.dual = 0, and neither ⊥ nor 0 is directly derivable.

    This creates mutual impossibility:
    - CPTyped [] impossible: any cut needs ⊥ or 0 singleton
    - CPTyped [x:⊥] impossible: botR needs CPTyped []
    - CPTyped [x:0] impossible: no direct rule, cut/mix recurse

    The full proof requires analyzing 2-element contexts for cuts on singleton bad contexts,
    showing that contexts like [x:⊥, y:a] are never derivable for any a (the ending type
    constrains which rules apply, and none can have ⊥ or 0 in non-final position except
    via topR which ends in ⊤). This is tracked as future work. -/

/-! ### Context-Based Inversion for Singleton Contexts

    These lemmas determine process structure from typing on singleton contexts.
    For singleton [x:τ], only specific typing rules apply based on τ. -/

/-- If CPTyped [x:1] p then p = .emptyOut x OR p is a cut/mix that can reduce.
    For the progress theorem, we need to know the process structure to identify
    principal cuts. This lemma provides the key case split. -/
lemma CPTyped.singleton_one_cases (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .one] p) :
    (p = .emptyOut x) ∨
    (∃ y a q, p = .nu y a q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x .one] = ctx at h
  cases h with
  | oneR x' =>
    simp only [mkAssign] at hctx
    left
    cases hctx; rfl
  | topR Γ' y p' =>
    -- Type ⊤ ≠ 1, contradiction
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact absurd this.2 (by decide)
  | ax x' w a =>
    -- Length 2 ≠ 1
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | cut Γ' Δ' x' a' p' q' _ _ =>
    -- p = .nu x' a' (.par p' q')
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    -- p = .par p' q'
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:⊥] p then p = .emptyInp x p' for some p', OR p is a cut/mix. -/
lemma CPTyped.singleton_bot_cases (x : Chan) (p : CPProc)
    (h : CPTyped [mkAssign x .bot] p) :
    (∃ p', p = .emptyInp x p' ∧ CPTyped [] p') ∨
    (∃ y a q, p = .nu y a q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x .bot] = ctx at h
  cases h with
  | botR Γ' x' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ, hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, _⟩ := hAssign
    subst hΓ hchan
    left
    exact ⟨p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⊗B] p then p = .out x y p' q' (tensor output), OR p is a cut/mix. -/
lemma CPTyped.singleton_tensor_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.tensor a b)] p) :
    (∃ y p' q', p = .out x y p' q' ∧ CPTyped [mkAssign y a] p' ∧ CPTyped [mkAssign x b] q') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.tensor a b)] = ctx at h
  cases h with
  | tensorR Γ' Δ' x' y' a' b' p' q' hp hq =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓΔ, hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan
    have hΓ'_nil := List.append_eq_nil_iff.mp hΓΔ.symm |>.1
    have hΔ'_nil := List.append_eq_nil_iff.mp hΓΔ.symm |>.2
    subst hΓ'_nil hΔ'_nil
    left
    simp only [List.nil_append] at hp hq
    exact ⟨y', p', q', rfl, hp, hq⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⅋B] p then p = .inp x y p' (par input), OR p is a cut/mix. -/
lemma CPTyped.singleton_par_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.par a b)] p) :
    (∃ y p', p = .inp x y p' ∧ CPTyped [mkAssign y a, mkAssign x b] p') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.par a b)] = ctx at h
  cases h with
  | parR Γ' x' y' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp
    exact ⟨y', p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A⊕B] p then p = .inl x p' or .inr x p' (additive selection), OR p is a cut/mix. -/
lemma CPTyped.singleton_addDisj_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.addDisj a b)] p) :
    (∃ p', p = .inl x p' ∧ CPTyped [mkAssign x a] p') ∨
    (∃ p', p = .inr x p' ∧ CPTyped [mkAssign x b] p') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.addDisj a b)] = ctx at h
  cases h with
  | addDisjR1 Γ' x' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp
    exact ⟨p', rfl, hp⟩
  | addDisjR2 Γ' x' a' b' p' hp =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    right; left
    simp only [List.nil_append] at hp
    exact ⟨p', rfl, hp⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addConjR Γ' x' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right; right
    exact ⟨p', q', rfl⟩

/-- If CPTyped [x:A&B] p then p = .case x p' q' (additive branching), OR p is a cut/mix. -/
lemma CPTyped.singleton_addConj_cases (x : Chan) (a b : CLLProp) (p : CPProc)
    (h : CPTyped [mkAssign x (.addConj a b)] p) :
    (∃ p' q', p = .case x p' q' ∧ CPTyped [mkAssign x a] p' ∧ CPTyped [mkAssign x b] q') ∨
    (∃ y c q, p = .nu y c q) ∨
    (∃ q r, p = .par q r) := by
  generalize hctx : [mkAssign x (.addConj a b)] = ctx at h
  cases h with
  | addConjR Γ' x' a' b' p' q' hp hq =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have ⟨hΓ', hAssign⟩ := List.append_singleton_inj.mp hctx
    simp only [TypeAssign.mk.injEq] at hAssign
    obtain ⟨hchan, hprop⟩ := hAssign
    cases hprop
    subst hchan hΓ'
    left
    simp only [List.nil_append] at hp hq
    exact ⟨p', q', rfl, hp, hq⟩
  | topR Γ' y p' =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | ax x' w a' =>
    simp only [mkAssign] at hctx
    have hlen := congrArg List.length hctx
    simp at hlen
  | oneR x' =>
    simp only [mkAssign] at hctx
    have := congrArg TypeAssign.prop (List.cons.inj hctx).1
    simp at this
  | cut Γ' Δ' x' a' p' q' _ _ =>
    right; left
    exact ⟨x', a', .par p' q', rfl⟩
  | tensorR Γ' Δ' x' y' a' b' p' q' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | parR Γ' x' a' b' p' _ _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR1 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | addDisjR2 Γ' x' a' b' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | botR Γ' x' p' _ =>
    simp only [mkAssign] at hctx
    rw [← List.nil_append [_]] at hctx
    have := List.append_singleton_inj.mp hctx |>.2
    simp only [TypeAssign.mk.injEq] at this
    exact nomatch this.2
  | mix Γ' Δ' p' q' _ _ =>
    right; right
    exact ⟨p', q', rfl⟩


/-! ### Unfinished context analysis

The original depth-induction attempts are archived in the upstream Git
history. Their statements and admission dependencies are recorded in
`artifacts/integration-20261028/legacy-session-claims.json`.
-/

/- Unproved legacy claim: see the integration research-status ledger. -/

/-- Helper: substitute channel in context assignment list -/
def Context.substChan (ctx : Context) (y z : Chan) : Context :=
  ctx.map fun a => ⟨if a.chan == z then y else a.chan, a.prop⟩

/- Unproved legacy claim: see the integration research-status ledger. -/

/-! ## Examples -/

/-- Example: identity process (forwarder) -/
def idProc (x w : Chan) : CPProc := .link x w

/-- Identity is well-typed -/
example (x w : Chan) (a : CLLProp) :
    CPTyped [mkAssign x a, mkAssign w a.dual] (idProc x w) :=
  CPTyped.ax x w a


/-! ## Checked counterexamples for the unconstrained legacy relation -/

/-- The link rule permits the same channel at both endpoints. -/
theorem CPTyped.context_linearity_not_forced :
    ∃ (Γ : Context) (p : CPProc), CPTyped Γ p ∧ ¬ Γ.linear := by
  refine ⟨[mkAssign "x" .one, mkAssign "x" .bot], .link "x" "x",
    CPTyped.ax "x" "x" .one, ?_⟩
  intro linear
  have equal := linear ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  exact Nat.zero_ne_one (congrArg Fin.val equal)

/-- The unrestricted top rule can type a process using an absent channel. -/
theorem CPTyped.free_channel_coverage_not_forced :
    ∃ (Γ : Context) (p : CPProc), CPTyped Γ p ∧
      ∃ c ∈ p.freeChans, c ∉ Γ.chans := by
  refine ⟨[mkAssign "x" .top], .link "y" "y",
    CPTyped.topR [] "x" (.link "y" "y"), "y", ?_, ?_⟩
  · simp [CPProc.freeChans]
  · simp [Context.chans, mkAssign]

#print axioms CPTyped.context_linearity_not_forced
#print axioms CPTyped.free_channel_coverage_not_forced

end Mettapedia.AutoBooks.ClaudeProcWam.ProcessCalculi
