/-
Loop persistence for the raw merge-insertion steps.

The merge fold's conditional invariant peels backward from the public
loop-filter fact: to use the induction hypothesis at `source`, a loop-free
extended record must certify a loop-free `source`.  This file proves the two
raw (non-reconciliation) cases:

* `hasLoop_false_of_addValRaw_fresh` — a loop-free `addValRaw source key
  value` with `classValues source key = []` certifies loop-free `source`.

The engine is two general facts about the bounded resolver:

* **Success replay** (`resolveAtomAux_some_of_cons_val_fresh`): with the
  equality graph unchanged and the fresh key's class valueless in `source`,
  the source resolution tree is the extended tree pruned to immediate
  successes at the fresh class, so extended success replays in `source` at
  the same fuel and visited set.

* **Fuel canonicity** (`resolveAtomAux_some_at_resolutionFuel`): success at
  any fuel implies success at the canonical `resolutionFuel` budget.  Along
  any successful path every value jump passes the visited guard and then
  pushes its whole class, so the jumped classes are pairwise disjoint and
  each stored value pays for its own descent: failure at the canonical
  budget is always a genuine cycle, never budget shortfall.
-/
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! ## Generic list accounting -/

private theorem sum_drop_le {α : Type} :
    ∀ (l : List α) (g g' : α → Nat) (a : α), a ∈ l →
      (∀ w ∈ l, g' w ≤ g w) → g' a = 0 →
      (l.map g').sum + g a ≤ (l.map g).sum
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | head :: tail, g, g', a, ha, hmono, hzero => by
    simp only [List.map_cons, List.sum_cons]
    cases List.mem_cons.mp ha with
    | inl heq =>
      subst heq
      have htail : (tail.map g').sum ≤ (tail.map g).sum := by
        apply List.sum_le_sum
        intro w hw
        exact hmono w (List.mem_cons_of_mem _ hw)
      omega
    | inr htail =>
      have hhead : g' head ≤ g head :=
        hmono head List.mem_cons_self
      have := sum_drop_le tail g g' a htail
        (fun w hw => hmono w (List.mem_cons_of_mem _ hw)) hzero
      omega

/-! ## Class-machinery facts -/

private theorem lookupVal_mem' :
    ∀ {lb : Metta.Bindings} {x : String} {a : Metta.Atom},
      Metta.Bindings.lookupVal lb x = some a →
      Metta.BindingRel.val x a ∈ lb
  | [], _, _, h => by simp [Metta.Bindings.lookupVal] at h
  | .val y v :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    by_cases hxy : (x == y) = true
    · rw [if_pos hxy] at h
      cases h
      have : x = y := by simpa using hxy
      subst this
      exact List.mem_cons_self
    · rw [if_neg hxy] at h
      exact List.mem_cons_of_mem _ (lookupVal_mem' h)
  | .eq _ _ :: rest, x, a, h => by
    simp only [Metta.Bindings.lookupVal] at h
    exact List.mem_cons_of_mem _ (lookupVal_mem' h)

private theorem mem_eqVarsFold_mono {v : String} :
    ∀ (l : Metta.Bindings) (acc : List String), v ∈ acc →
      v ∈ l.foldl (fun acc r => match r with
        | Metta.BindingRel.eq x y =>
            let acc := if acc.contains y then acc else acc ++ [y]
            if acc.contains x then acc else acc ++ [x]
        | _ => acc) acc
  | [], _, hv => hv
  | rel :: rest, acc, hv => by
    simp only [List.foldl_cons]
    apply mem_eqVarsFold_mono rest
    cases rel with
    | val _ _ => exact hv
    | eq x y =>
      have hstep : ∀ acc2 : List String, v ∈ acc2 →
          v ∈ (if acc2.contains x then acc2 else acc2 ++ [x]) := by
        intro acc2 hv2
        split
        · exact hv2
        · exact List.mem_append_left _ hv2
      have h1 : v ∈ (if acc.contains y then acc else acc ++ [y]) := by
        split
        · exact hv
        · exact List.mem_append_left _ hv
      exact hstep _ h1

private theorem endpoint_mem_eqVarsInOrder
    {lb : Metta.Bindings} {a b : String}
    (hmem : Metta.BindingRel.eq a b ∈ lb) :
    a ∈ Metta.Bindings.eqVarsInOrder lb ∧
      b ∈ Metta.Bindings.eqVarsInOrder lb := by
  unfold Metta.Bindings.eqVarsInOrder
  have hmem' : Metta.BindingRel.eq a b ∈ lb.reverse :=
    List.mem_reverse.mpr hmem
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hmem'
  rw [hsplit, List.foldl_append, List.foldl_cons]
  set seed := pre.foldl (fun acc r => match r with
    | Metta.BindingRel.eq x y =>
        let acc := if acc.contains y then acc else acc ++ [y]
        if acc.contains x then acc else acc ++ [x]
    | _ => acc) [] with hseed
  have hstep : ∀ acc2 : List String, b ∈ acc2 →
      a ∈ (if acc2.contains a then acc2 else acc2 ++ [a]) ∧
        b ∈ (if acc2.contains a then acc2 else acc2 ++ [a]) := by
    intro acc2 hb
    constructor
    · split
      · rename_i ha
        simpa using ha
      · exact List.mem_append_right _ (by simp)
    · split
      · exact hb
      · exact List.mem_append_left _ hb
  have hb2 : b ∈ (if seed.contains b then seed else seed ++ [b]) := by
    split
    · rename_i hbc
      simpa using hbc
    · exact List.mem_append_right _ (by simp)
  obtain ⟨hafin, hbfin⟩ :=
    hstep (if seed.contains b then seed else seed ++ [b]) hb2
  exact ⟨mem_eqVarsFold_mono post _ hafin,
    mem_eqVarsFold_mono post _ hbfin⟩

private theorem self_mem_eqClass
    (lb : Metta.Bindings) (x : String) :
    x ∈ Metta.Bindings.eqClass lb x :=
  mem_leaEqClass_iff_reachable.mpr .rfl

private theorem eqClass_mem_congr
    {lb : Metta.Bindings} {x y : String}
    (hxy : y ∈ Metta.Bindings.eqClass lb x) (w : String) :
    w ∈ Metta.Bindings.eqClass lb y ↔
      w ∈ Metta.Bindings.eqClass lb x := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable]
  have hreach := mem_leaEqClass_iff_reachable.mp hxy
  exact ⟨fun h => hreach.trans h, fun h => hreach.symm.trans h⟩

private theorem mem_eqVarsInOrder_of_reachable_ne
    {lb : Metta.Bindings} {x c : String} (hne : x ≠ c)
    (hreach : (EqualityClosure.edgeGraph
      (leaEqualityEdges lb)).Reachable x c) :
    x ∈ Metta.Bindings.eqVarsInOrder lb := by
  apply hreach.elim
  intro walk
  cases walk with
  | nil => exact absurd rfl hne
  | cons hadj tail =>
    rcases (EqualityClosure.edgeGraph_adj_iff.mp hadj).2 with
      hedge | hedge
    · exact (endpoint_mem_eqVarsInOrder
        (mem_leaEqualityEdges_iff.mp hedge)).1
    · exact (endpoint_mem_eqVarsInOrder
        (mem_leaEqualityEdges_iff.mp hedge)).2

private theorem self_mem_eqClassOrdered
    (lb : Metta.Bindings) (x : String) :
    x ∈ Metta.Bindings.eqClassOrdered lb x := by
  unfold Metta.Bindings.eqClassOrdered
  cases hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun y => (Metta.Bindings.eqClass lb x).contains y) with
  | nil => simp
  | cons c cs =>
    have hc : c ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun y => (Metta.Bindings.eqClass lb x).contains y) := by
      rw [hfilter]; exact List.mem_cons_self
    have hcclass : c ∈ Metta.Bindings.eqClass lb x := by
      simpa using (List.mem_filter.mp hc).2
    have hx : x ∈ Metta.Bindings.eqVarsInOrder lb := by
      by_cases hxc : x = c
      · subst hxc
        exact (List.mem_filter.mp hc).1
      · exact mem_eqVarsInOrder_of_reachable_ne hxc
          (mem_leaEqClass_iff_reachable.mp hcclass)
    have hxf : x ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun y => (Metta.Bindings.eqClass lb x).contains y) :=
      List.mem_filter.mpr ⟨hx, by simpa using self_mem_eqClass lb x⟩
    rw [hfilter] at hxf
    try rw [hfilter]
    exact hxf

private theorem eqClassOrdered_congr_of_mem
    {lb : Metta.Bindings} {x y : String}
    (hxy : y ∈ Metta.Bindings.eqClass lb x) :
    Metta.Bindings.eqClassOrdered lb y =
      Metta.Bindings.eqClassOrdered lb x := by
  unfold Metta.Bindings.eqClassOrdered
  have hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun w => (Metta.Bindings.eqClass lb y).contains w) =
      (Metta.Bindings.eqVarsInOrder lb).filter
        (fun w => (Metta.Bindings.eqClass lb x).contains w) := by
    apply List.filter_congr
    intro w _
    have := eqClass_mem_congr hxy w
    by_cases hw : w ∈ Metta.Bindings.eqClass lb x
    · simp [hw, this.mpr hw]
    · have hwy : w ∉ Metta.Bindings.eqClass lb y :=
        fun hcontra => hw (this.mp hcontra)
      simp [hw, hwy]
  rw [hfilter]
  cases hcase : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun w => (Metta.Bindings.eqClass lb x).contains w) with
  | nil =>
    by_cases hxyeq : y = x
    · rw [hxyeq]
    · exfalso
      have hy : y ∈ Metta.Bindings.eqVarsInOrder lb :=
        mem_eqVarsInOrder_of_reachable_ne hxyeq
          (mem_leaEqClass_iff_reachable.mp hxy).symm
      have : y ∈ (Metta.Bindings.eqVarsInOrder lb).filter
          (fun w => (Metta.Bindings.eqClass lb x).contains w) :=
        List.mem_filter.mpr ⟨hy, by simpa using hxy⟩
      rw [hcase] at this
      exact absurd this (List.not_mem_nil)
  | cons c cs => rfl

private theorem mem_eqClassOrdered_cases'
    {lb : Metta.Bindings} {x y : String}
    (h : y ∈ Metta.Bindings.eqClassOrdered lb x) :
    y = x ∨ y ∈ Metta.Bindings.eqClass lb x := by
  unfold Metta.Bindings.eqClassOrdered at h
  cases hfilter : (Metta.Bindings.eqVarsInOrder lb).filter
      (fun z => (Metta.Bindings.eqClass lb x).contains z) with
  | nil =>
    rw [hfilter] at h
    simp only [List.mem_singleton] at h
    exact Or.inl h
  | cons head tail =>
    rw [hfilter] at h
    have hmem : y ∈ (Metta.Bindings.eqVarsInOrder lb).filter
        (fun z => (Metta.Bindings.eqClass lb x).contains z) := by
      rw [hfilter]; exact h
    exact Or.inr (by simpa using (List.mem_filter.mp hmem).2)

/-! ## Invariance of the class machinery under a value cons -/

section ConsVal

variable (source : Metta.Bindings) (key : String) (value : Metta.Atom)

private theorem leaEqualityEdges_cons_val :
    leaEqualityEdges (Metta.BindingRel.val key value :: source) =
      leaEqualityEdges source := rfl

private theorem eqClass_cons_val_mem (z w : String) :
    w ∈ Metta.Bindings.eqClass
        (Metta.BindingRel.val key value :: source) z ↔
      w ∈ Metta.Bindings.eqClass source z := by
  rw [mem_leaEqClass_iff_reachable, mem_leaEqClass_iff_reachable,
    leaEqualityEdges_cons_val]

private theorem eqClassOrdered_cons_val (z : String) :
    Metta.Bindings.eqClassOrdered
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.eqClassOrdered source z := by
  unfold Metta.Bindings.eqClassOrdered
  rw [leaEqVarsInOrder_cons_val]
  have hfilter : (Metta.Bindings.eqVarsInOrder source).filter
      (fun y => (Metta.Bindings.eqClass
        (Metta.BindingRel.val key value :: source) z).contains y) =
      (Metta.Bindings.eqVarsInOrder source).filter
        (fun y => (Metta.Bindings.eqClass source z).contains y) := by
    apply List.filter_congr
    intro w _
    have := eqClass_cons_val_mem source key value z w
    by_cases hw : w ∈ Metta.Bindings.eqClass source z
    · simp [hw, this.mpr hw]
    · have hw' : w ∉ Metta.Bindings.eqClass
          (Metta.BindingRel.val key value :: source) z :=
        fun hcontra => hw (this.mp hcontra)
      simp [hw, hw']
  rw [hfilter]

private theorem eqRepresentative_cons_val (z : String) :
    Metta.Bindings.eqRepresentative
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.eqRepresentative source z := by
  unfold Metta.Bindings.eqRepresentative
  rw [eqClassOrdered_cons_val]

private theorem lookupVal_cons_val (z : String) :
    Metta.Bindings.lookupVal
        (Metta.BindingRel.val key value :: source) z =
      if (z == key) = true then some value
      else Metta.Bindings.lookupVal source z := by
  simp only [Metta.Bindings.lookupVal]

private theorem classValues_cons_val_untouched {z : String}
    (hkey : key ∉ Metta.Bindings.eqClassOrdered source z) :
    Metta.Bindings.classValues
        (Metta.BindingRel.val key value :: source) z =
      Metta.Bindings.classValues source z := by
  unfold Metta.Bindings.classValues
  rw [eqClassOrdered_cons_val]
  apply List.filterMap_congr
  intro w hw
  rw [lookupVal_cons_val]
  have hne : (w == key) ≠ true := by
    intro hcontra
    have : w = key := by simpa using hcontra
    subst this
    exact hkey hw
  rw [if_neg hne]

private theorem classValues_source_nil_of_key_class {z : String}
    (hfresh : Metta.Bindings.classValues source key = [])
    (hkey : key ∈ Metta.Bindings.eqClassOrdered source z) :
    Metta.Bindings.classValues source z = [] := by
  rcases mem_eqClassOrdered_cases' hkey with heq | hclass
  · subst heq; exact hfresh
  · have hordered : Metta.Bindings.eqClassOrdered source key =
        Metta.Bindings.eqClassOrdered source z :=
      eqClassOrdered_congr_of_mem hclass
    unfold Metta.Bindings.classValues at hfresh ⊢
    rw [← hordered]
    exact hfresh

end ConsVal

/-! ## Success replay: extended cons-val record to source -/

private theorem mapM_some_of_pointwise
    {f g : Metta.Atom → Option Metta.Atom} :
    ∀ (xs : List Metta.Atom) (ys : List Metta.Atom),
      xs.mapM f = some ys →
      (∀ z ∈ xs, ∀ w, f z = some w → (g z).isSome = true) →
      ∃ ws, xs.mapM g = some ws
  | [], _, _, _ => ⟨[], rfl⟩
  | x :: xs, ys, h, hpt => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp
          (hpt x List.mem_cons_self xr hx)
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs xsr hxs
          (fun z hz => hpt z (List.mem_cons_of_mem _ hz))
        exact ⟨w :: ws, by simp [List.mapM_cons, hw, hws]⟩

/-- Extended success replays in the source at the same fuel and visited
set: the source resolution tree is the extended tree pruned to immediate
successes at the fresh key's (valueless) class. -/
private theorem resolveAtomAux_some_of_cons_val_fresh
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfresh : Metta.Bindings.classValues source key = []) :
    ∀ (fuel : Nat) (visited : List String) (a r : Metta.Atom),
      Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.val key value :: source) fuel visited a =
        some r →
      (Metta.Bindings.resolveAtomAux source fuel visited a).isSome =
        true := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a r h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a r h
    cases a with
    | sym s => simp [Metta.Bindings.resolveAtomAux]
    | gnd g => simp [Metta.Bindings.resolveAtomAux]
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM (Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.val key value :: source) fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs ys hmap
          (fun z _ w hw => ih visited z w hw)
        rw [hws]
        simp
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      rw [eqClassOrdered_cons_val] at h
      by_cases hguard : ((Metta.Bindings.eqClassOrdered source z).any
          visited.contains) = true
      · rw [if_pos hguard] at h
        cases h
      · rw [if_neg hguard] at h
        rw [if_neg hguard]
        by_cases hkey : key ∈ Metta.Bindings.eqClassOrdered source z
        · rw [classValues_source_nil_of_key_class source key hfresh hkey]
          simp
        · rw [classValues_cons_val_untouched source key value hkey] at h
          cases hvalues : Metta.Bindings.classValues source z with
          | nil =>
            rw [hvalues] at h
            simp
          | cons v rest =>
            rw [hvalues] at h
            cases v with
            | var y =>
              by_cases hcontains :
                  y ∈ Metta.Bindings.eqClassOrdered source z
              · by_cases hlen :
                    (Metta.Bindings.eqClassOrdered source z).length = 1
                · simp [hcontains, hlen] at h
                · simp [hcontains, hlen]
              · have hrec : Metta.Bindings.resolveAtomAux
                    (Metta.BindingRel.val key value :: source) fuel
                    (Metta.Bindings.eqClassOrdered source z ++ visited)
                    (Metta.Atom.var y) = some r := by
                  simpa [hcontains] using h
                simpa [hcontains] using ih _ _ _ hrec
            | sym s =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.sym s) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec
            | gnd g =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.gnd g) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec
            | expr atoms =>
              have hrec : Metta.Bindings.resolveAtomAux
                  (Metta.BindingRel.val key value :: source) fuel
                  (Metta.Bindings.eqClassOrdered source z ++ visited)
                  (Metta.Atom.expr atoms) = some r := by
                simpa using h
              simpa using ih _ _ _ hrec

/-! ## Fuel canonicity -/

/-- The unspent value budget: every stored value of a class not yet touched
by the visited set still pays for its own descent plus one jump step. -/
private def remBudget (b : Metta.Bindings) (visited : List String) : Nat :=
  (b.map (fun rel => match rel with
    | Metta.BindingRel.val x v =>
        if (Metta.Bindings.eqClassOrdered b x).any visited.contains then 0
        else v.size + 1
    | Metta.BindingRel.eq _ _ => 0)).sum

private theorem remBudget_term_mono (b : Metta.Bindings)
    {small large : List String} (hsub : ∀ s ∈ small, s ∈ large)
    (rel : Metta.BindingRel) :
    (match rel with
      | Metta.BindingRel.val x v =>
          if (Metta.Bindings.eqClassOrdered b x).any large.contains then 0
          else v.size + 1
      | Metta.BindingRel.eq _ _ => 0) ≤
    (match rel with
      | Metta.BindingRel.val x v =>
          if (Metta.Bindings.eqClassOrdered b x).any small.contains then 0
          else v.size + 1
      | Metta.BindingRel.eq _ _ => 0) := by
  cases rel with
  | eq _ _ => simp
  | val x v =>
    simp only []
    by_cases hsmall : ((Metta.Bindings.eqClassOrdered b x).any
        small.contains) = true
    · have hlarge : ((Metta.Bindings.eqClassOrdered b x).any
          large.contains) = true := by
        rw [List.any_eq_true] at hsmall ⊢
        obtain ⟨w, hw, hcontains⟩ := hsmall
        exact ⟨w, hw, by
          have : w ∈ small := by simpa using hcontains
          simpa using hsub w this⟩
      rw [if_pos hsmall, if_pos hlarge]
    · rw [if_neg hsmall]
      split <;> omega

/-- Jumping into a class value strictly repays the budget: the value's own
relation drops out of the unspent sum. -/
private theorem remBudget_jump
    {b : Metta.Bindings} {x : String} {v : Metta.Atom} {visited : List String}
    (hguard : ((Metta.Bindings.eqClassOrdered b x).any
      visited.contains) = false)
    (hhead : v ∈ Metta.Bindings.classValues b x) :
    remBudget b (Metta.Bindings.eqClassOrdered b x ++ visited) +
      (v.size + 1) ≤ remBudget b visited := by
  unfold Metta.Bindings.classValues at hhead
  obtain ⟨y, hy, hlookup⟩ := List.mem_filterMap.mp hhead
  have hyv : Metta.BindingRel.val y v ∈ b := lookupVal_mem' hlookup
  have hyclass : Metta.Bindings.eqClassOrdered b y =
      Metta.Bindings.eqClassOrdered b x := by
    rcases mem_eqClassOrdered_cases' hy with heq | hclass
    · rw [heq]
    · exact eqClassOrdered_congr_of_mem hclass
  have hdrop := sum_drop_le b
    (fun rel => match rel with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any visited.contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0)
    (fun rel => match rel with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any
              (Metta.Bindings.eqClassOrdered b x ++ visited).contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0)
    (Metta.BindingRel.val y v) hyv
    (fun w _ => remBudget_term_mono b
      (fun s hs => List.mem_append_right _ hs) w)
    (by
      simp only []
      have hyin : ((Metta.Bindings.eqClassOrdered b y).any
          (Metta.Bindings.eqClassOrdered b x ++ visited).contains) =
            true := by
        rw [List.any_eq_true]
        refine ⟨y, self_mem_eqClassOrdered b y, ?_⟩
        have : y ∈ Metta.Bindings.eqClassOrdered b x ++ visited :=
          List.mem_append_left _ hy
        simpa using this
      rw [if_pos hyin])
  have hterm : (match Metta.BindingRel.val y v with
      | Metta.BindingRel.val w u =>
          if (Metta.Bindings.eqClassOrdered b w).any visited.contains then 0
          else u.size + 1
      | Metta.BindingRel.eq _ _ => 0) = v.size + 1 := by
    simp only []
    rw [hyclass, hguard]
    simp
  rw [hterm] at hdrop
  exact hdrop

private theorem mapM_transfer
    {f g : Metta.Atom → Option Metta.Atom} :
    ∀ (xs ys : List Metta.Atom),
      xs.mapM f = some ys →
      (∀ z ∈ xs, ∀ w, f z = some w → g z = some w) →
      xs.mapM g = some ys
  | [], _, h, _ => h
  | x :: xs, ys, h, hpt => by
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some xr =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some xsr =>
        have hys : xr :: xsr = ys := by
          simpa [List.mapM_cons, hx, hxs] using h
        have hgx := hpt x List.mem_cons_self xr hx
        have hgxs := mapM_transfer xs xsr hxs
          (fun z hz => hpt z (List.mem_cons_of_mem _ hz))
        rw [← hys]
        simp [List.mapM_cons, hgx, hgxs]

private theorem persist_size_pos (a : Metta.Atom) : 0 < a.size := by
  cases a <;> simp only [Metta.Atom.size] <;> omega

private theorem persist_size_lt_of_mem {a : Metta.Atom} :
    ∀ {l : List Metta.Atom}, a ∈ l →
      a.size < (Metta.Atom.expr l).size
  | x :: xs, h => by
    cases List.mem_cons.mp h with
    | inl h1 =>
      subst h1
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons]
      omega
    | inr h2 =>
      have := persist_size_lt_of_mem h2
      simp only [Metta.Atom.size, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- **Fuel canonicity core.**  A successful bounded resolution also succeeds
— with the same result — at the canonical budget `a.size + remBudget + 1`:
every jump on a successful path strictly repays the budget. -/
private theorem resolveAtomAux_some_at_budget'
    {b : Metta.Bindings} :
    ∀ (fuel : Nat) (visited : List String) (a r : Metta.Atom),
      Metta.Bindings.resolveAtomAux b fuel visited a = some r →
      Metta.Bindings.resolveAtomAux b
          (a.size + remBudget b visited + 1) visited a = some r := by
  intro fuel
  induction fuel with
  | zero =>
    intro visited a r h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visited a r h
    cases a with
    | sym s =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      exact h
    | gnd g =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      exact h
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM
          (Metta.Bindings.resolveAtomAux b fuel visited) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        rw [hmap] at h
        have htransfer := mapM_transfer
          (f := Metta.Bindings.resolveAtomAux b fuel visited)
          (g := Metta.Bindings.resolveAtomAux b
            ((Metta.Atom.expr xs).size + remBudget b visited) visited)
          xs ys hmap (by
            intro z hz w hw
            have hcanon := ih visited z w hw
            have hle : z.size + remBudget b visited + 1 ≤
                (Metta.Atom.expr xs).size + remBudget b visited := by
              have := persist_size_lt_of_mem hz
              omega
            obtain ⟨extra, hextra⟩ := Nat.le.dest hle
            rw [← hextra]
            exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_add_fuel extra hcanon)
        rw [htransfer]
        exact h
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      by_cases hguard : ((Metta.Bindings.eqClassOrdered b z).any
          visited.contains) = true
      · rw [if_pos hguard] at h
        cases h
      · rw [if_neg hguard] at h
        rw [if_neg hguard]
        cases hvalues : Metta.Bindings.classValues b z with
        | nil =>
          rw [hvalues] at h
          simpa using h
        | cons v rest =>
          rw [hvalues] at h
          have hguard' : ((Metta.Bindings.eqClassOrdered b z).any
              visited.contains) = false := by
            simpa using hguard
          have hhead : v ∈ Metta.Bindings.classValues b z := by
            rw [hvalues]; exact List.mem_cons_self
          have hjump := remBudget_jump hguard' hhead
          have hinner : ∀ r',
              Metta.Bindings.resolveAtomAux b fuel
                  (Metta.Bindings.eqClassOrdered b z ++ visited) v =
                some r' →
              Metta.Bindings.resolveAtomAux b
                  ((Metta.Atom.var z).size + remBudget b visited)
                  (Metta.Bindings.eqClassOrdered b z ++ visited) v =
                some r' := by
            intro r' hr'
            have hcanon := ih _ _ _ hr'
            have hle : v.size + remBudget b
                  (Metta.Bindings.eqClassOrdered b z ++ visited) + 1 ≤
                (Metta.Atom.var z).size + remBudget b visited := by
              simp only [Metta.Atom.size]
              omega
            obtain ⟨extra, hextra⟩ := Nat.le.dest hle
            rw [← hextra]
            exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_add_fuel extra hcanon
          cases v with
          | var y =>
            by_cases hcontains :
                y ∈ Metta.Bindings.eqClassOrdered b z
            · by_cases hlen :
                  (Metta.Bindings.eqClassOrdered b z).length = 1
              · simp [hcontains, hlen] at h
              · simpa [hcontains, hlen] using h
            · have hrec : Metta.Bindings.resolveAtomAux b fuel
                  (Metta.Bindings.eqClassOrdered b z ++ visited)
                  (Metta.Atom.var y) = some r := by
                simpa [hcontains] using h
              simpa [hcontains] using hinner r hrec
          | sym s =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.sym s) = some r := by
              simpa using h
            simpa using hinner r hrec
          | gnd g =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.gnd g) = some r := by
              simpa using h
            simpa using hinner r hrec
          | expr atoms =>
            have hrec : Metta.Bindings.resolveAtomAux b fuel
                (Metta.Bindings.eqClassOrdered b z ++ visited)
                (Metta.Atom.expr atoms) = some r := by
              simpa using h
            simpa using hinner r hrec

/-- **Fuel canonicity.**  Success at any fuel implies success at the
canonical `resolutionFuel` budget.  Failure at the canonical budget is
therefore always a genuine cyclic dependency, never budget shortfall. -/
theorem resolveAtomAux_some_at_resolutionFuel
    {b : Metta.Bindings} {fuel : Nat} {a r : Metta.Atom}
    (h : Metta.Bindings.resolveAtomAux b fuel [] a = some r) :
    Metta.Bindings.resolveAtomAux b
        (Metta.Bindings.resolutionFuel b a) [] a = some r := by
  have hcanon := resolveAtomAux_some_at_budget' fuel [] a r h
  have hle : a.size + remBudget b [] + 1 ≤
      Metta.Bindings.resolutionFuel b a := by
    unfold Metta.Bindings.resolutionFuel
    have hsum : remBudget b [] ≤
        (b.map Metta.Bindings.relationResolutionFuel).sum := by
      unfold remBudget
      apply List.sum_le_sum
      intro rel _
      cases rel with
      | val x v =>
        simp only [Metta.Bindings.relationResolutionFuel]
        split <;> omega
      | eq _ _ =>
        simp [Metta.Bindings.relationResolutionFuel]
    omega
  obtain ⟨extra, hextra⟩ := Nat.le.dest hle
  rw [← hextra]
  exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_add_fuel extra hcanon

/-! ## Disjoint binding frames at the native resolution budget -/

/-- Native structural budgets represent the same observation whenever all
explicit budgets agree, because successful native resolution has a proved
canonical budget on either store. -/
theorem leaResolveAtomAux_canonical_eq_of_fuel_agreement
    (left right : Metta.Bindings) (atom : Metta.Atom)
    (agreement : ∀ fuel,Metta.Bindings.resolveAtomAux left fuel [] atom =
      Metta.Bindings.resolveAtomAux right fuel [] atom) :
    Metta.Bindings.resolveAtomAux left (Metta.Bindings.resolutionFuel left atom) [] atom =
      Metta.Bindings.resolveAtomAux right (Metta.Bindings.resolutionFuel right atom) [] atom := by
  cases leftRun : Metta.Bindings.resolveAtomAux left
      (Metta.Bindings.resolutionFuel left atom) [] atom with
  | none =>
    cases rightRun : Metta.Bindings.resolveAtomAux right
        (Metta.Bindings.resolutionFuel right atom) [] atom with
    | none => rfl
    | some result =>
      have lift : Metta.Bindings.resolveAtomAux left
          (Metta.Bindings.resolutionFuel right atom) [] atom = some result := by
        rw [agreement]
        exact rightRun
      have canonical := resolveAtomAux_some_at_resolutionFuel lift
      rw [leftRun] at canonical
      cases canonical
  | some result =>
    have lower : Metta.Bindings.resolveAtomAux right
        (Metta.Bindings.resolutionFuel left atom) [] atom = some result := by
      rw [← agreement]
      exact leftRun
    exact (resolveAtomAux_some_at_resolutionFuel lower).symm

/-- Different native structural budgets observe the same isolated component:
the larger store does not turn a local cycle into a successful resolution. -/
theorem leaResolveAtomAux_canonical_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (atom : Metta.Atom) (outside : ∀ key ∈ atom.vars, key ∉ frame.vars) :
    Metta.Bindings.resolveAtomAux (front ++ frame)
        (Metta.Bindings.resolutionFuel (front ++ frame) atom) [] atom =
      Metta.Bindings.resolveAtomAux front
        (Metta.Bindings.resolutionFuel front atom) [] atom := by
  apply leaResolveAtomAux_canonical_eq_of_fuel_agreement
  intro fuel
  exact leaResolveAtomAux_append_frame disjoint fuel [] atom outside

/-- Complete native variable resolution is local to an isolated binding
component, including unknown-variable and cyclic-resolution outcomes. -/
theorem leaResolve_append_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ frame.vars) :
    Metta.Bindings.resolve (front ++ frame) key = Metta.Bindings.resolve front key := by
  simp only [Metta.Bindings.resolve,
    leaEqClassOrdered_append_frame disjoint outside,
    leaClassValues_append_frame disjoint outside]
  split
  · rfl
  · exact leaResolveAtomAux_canonical_append_frame disjoint (.var key)
      (by simpa [Metta.Atom.vars] using outside)

/-- Instantiation of local syntax depends only on its local binding component.
The local component may contain aliases or open compound values, and the frame
may itself be cyclic; every name mentioned on the local side must be separate. -/
theorem instantiate_append_disjoint_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (atom : Metta.Atom) (outside : ∀ key ∈ atom.vars, key ∉ frame.vars) :
    Metta.instantiate (front ++ frame) atom = Metta.instantiate front atom := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.instantiate_eq_of_resolve_on_vars
  intro key present
  exact leaResolve_append_frame disjoint (outside key present)

theorem leaResolveAtomAux_canonical_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (atom : Metta.Atom) (outside : ∀ key ∈ atom.vars,key ∉ front.vars) :
    Metta.Bindings.resolveAtomAux (front++frame)
        (Metta.Bindings.resolutionFuel (front++frame) atom) [] atom =
      Metta.Bindings.resolveAtomAux frame (Metta.Bindings.resolutionFuel frame atom) [] atom := by
  apply leaResolveAtomAux_canonical_eq_of_fuel_agreement
  intro fuel
  exact leaResolveAtomAux_append_left_frame disjoint fuel [] atom outside

theorem leaResolve_append_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    {key : String} (outside : key ∉ front.vars) :
    Metta.Bindings.resolve (front++frame) key = Metta.Bindings.resolve frame key := by
  simp only [Metta.Bindings.resolve,
    leaEqClassOrdered_append_left_frame disjoint outside,
    leaClassValues_append_left_frame disjoint outside]
  split
  · rfl
  · exact leaResolveAtomAux_canonical_append_left_frame disjoint (.var key)
      (by simpa [Metta.Atom.vars] using outside)

theorem instantiate_append_disjoint_left_frame
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (atom : Metta.Atom) (outside : ∀ key ∈ atom.vars,key ∉ front.vars) :
    Metta.instantiate (front++frame) atom = Metta.instantiate frame atom := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.instantiate_eq_of_resolve_on_vars
  intro key present
  exact leaResolve_append_left_frame disjoint (outside key present)

/-- Native loop detection on disjoint binding components is their Boolean
union. This uses the actual first-value resolver, including malformed records;
it does not assume that all values in a class have a common solution. -/
theorem hasLoop_append_disjoint
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars) :
    Metta.Bindings.hasLoop (front++frame) =
      (Metta.Bindings.hasLoop front || Metta.Bindings.hasLoop frame) := by
  let failed (bindings : Metta.Bindings) (key : String) : Bool :=
    (Metta.Bindings.resolveAtomAux bindings
      (Metta.Bindings.resolutionFuel bindings (.var key)) [] (.var key)).isNone
  have frontFailure (key : String) (member : key ∈ front.vars) :
      failed (front++frame) key = failed front key := by
    unfold failed
    rw [leaResolveAtomAux_canonical_append_frame disjoint (.var key)
      (by simpa [Metta.Atom.vars] using (List.disjoint_left.mp disjoint member))]
  have frameFailure (key : String) (member : key ∈ frame.vars) :
      failed (front++frame) key = failed frame key := by
    unfold failed
    rw [leaResolveAtomAux_canonical_append_left_frame disjoint (.var key)
      (by simpa [Metta.Atom.vars] using (List.disjoint_right.mp disjoint member))]
  have failures : (Metta.Bindings.vars (front++frame)).any (failed (front++frame)) =
      (front.vars.any (failed front) || frame.vars.any (failed frame)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,Bool.or_eq_true]
    constructor
    · rintro ⟨key,member,failure⟩
      rcases (bindings_vars_append_iff front frame key).mp member with inFront | inFrame
      · exact Or.inl ⟨key,inFront,(frontFailure key inFront).symm.trans failure⟩
      · exact Or.inr ⟨key,inFrame,(frameFailure key inFrame).symm.trans failure⟩
    · rintro (⟨key,member,failure⟩ | ⟨key,member,failure⟩)
      · exact ⟨key,(bindings_vars_append_iff front frame key).mpr (Or.inl member),
          (frontFailure key member).trans failure⟩
      · exact ⟨key,(bindings_vars_append_iff front frame key).mpr (Or.inr member),
          (frameFailure key member).trans failure⟩
  simp only [Metta.Bindings.hasLoop,List.any_append]
  rw [show (Metta.Bindings.vars (front++frame)).any
      (fun key => (Metta.Bindings.resolveAtomAux (front++frame)
        (Metta.Bindings.resolutionFuel (front++frame) (.var key)) [] (.var key)).isNone) =
      (front.vars.any (failed front) || frame.vars.any (failed frame)) from failures]
  dsimp only [failed]
  ac_rfl

theorem hasLoop_false_append_disjoint
    {front frame : Metta.Bindings} (disjoint : List.Disjoint front.vars frame.vars)
    (frontAdmitted : Metta.Bindings.hasLoop front=false)
    (frameAdmitted : Metta.Bindings.hasLoop frame=false) :
    Metta.Bindings.hasLoop (front++frame)=false := by
  rw [hasLoop_append_disjoint disjoint,frontAdmitted,frameAdmitted]
  rfl

/-! ## Fresh closed caller extension -/

private theorem outside_not_mem_ordered_class
    {source : Metta.Bindings} {key other : String}
    (hfresh : key ∉ Metta.Bindings.vars source) (hne : other ≠ key) :
    key ∉ Metta.Bindings.eqClassOrdered source other := by
  intro hmem
  have hclasses : Metta.Bindings.eqClassOrdered source key =
      Metta.Bindings.eqClassOrdered source other := by
    rcases mem_eqClassOrdered_cases' hmem with heq | hclass
    · rw [heq]
    · exact eqClassOrdered_congr_of_mem hclass
  have hself := self_mem_eqClassOrdered source other
  rw [← hclasses,
    (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.outside_class hfresh).1] at hself
  exact hne (List.mem_singleton.mp hself)

private theorem outside_class_value_vars
    {source : Metta.Bindings} {key other : String} {value : Metta.Atom}
    (hfresh : key ∉ Metta.Bindings.vars source)
    (hvalue : value ∈ Metta.Bindings.classValues source other) : key ∉ value.vars := by
  intro hin
  obtain ⟨owner, _, hlookup⟩ := List.mem_filterMap.mp hvalue
  have hstored := lookupVal_mem' hlookup
  apply hfresh
  simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨_, hstored, by simp [hin]⟩

/-- A fresh value relation cannot affect a successful read whose source term
does not mention its new key. This includes recursive reads through caller
aliases and compound values. -/
theorem resolveAtomAux_cons_val_fresh
    {source : Metta.Bindings} {key : String} (value : Metta.Atom)
    (hfresh : key ∉ Metta.Bindings.vars source) :
    ∀ (fuel : Nat) (visited : List String) (atom resolved : Metta.Atom),
      key ∉ atom.vars →
      Metta.Bindings.resolveAtomAux source fuel visited atom = some resolved →
      Metta.Bindings.resolveAtomAux (.val key value :: source) fuel visited atom =
        some resolved := by
  intro fuel
  induction fuel with
  | zero => intro visited atom resolved _ hresolve
            simp [Metta.Bindings.resolveAtomAux] at hresolve
  | succ fuel ih =>
    intro visited atom resolved hnot hresolve
    cases atom with
    | sym name => simpa [Metta.Bindings.resolveAtomAux] using hresolve
    | gnd ground => simpa [Metta.Bindings.resolveAtomAux] using hresolve
    | var other =>
      have hne : other ≠ key := by simpa [Metta.Atom.vars, eq_comm] using hnot
      have hclass := eqClassOrdered_cons_val source key value other
      have hrep := eqRepresentative_cons_val source key value other
      have hvalues := classValues_cons_val_untouched source key value
        (outside_not_mem_ordered_class hfresh hne)
      simp only [Metta.Bindings.resolveAtomAux, hclass, hrep, hvalues] at hresolve ⊢
      split at hresolve
      · contradiction
      · rename_i hclear
        rw [if_neg hclear]
        cases hvs : Metta.Bindings.classValues source other with
        | nil => simpa only [hvs] using hresolve
        | cons selected rest =>
          have hselected := outside_class_value_vars hfresh (hvs ▸ List.mem_cons_self)
          simp only [hvs] at hresolve ⊢
          cases selected with
          | var target =>
            dsimp only at hresolve ⊢
            by_cases htarget : (Metta.Bindings.eqClassOrdered source other).contains target = true
            · simp only [htarget, ↓reduceIte] at hresolve ⊢
              exact hresolve
            · simp only [htarget] at hresolve ⊢
              exact ih _ _ _ hselected hresolve
          | sym name => exact ih _ _ _ hselected hresolve
          | gnd ground => exact ih _ _ _ hselected hresolve
          | expr children => exact ih _ _ _ hselected hresolve
    | expr children =>
      simp only [Metta.Bindings.resolveAtomAux] at hresolve ⊢
      cases hmap : children.mapM (Metta.Bindings.resolveAtomAux source fuel visited) with
      | none => simp [hmap] at hresolve
      | some values =>
        have hmap' : children.mapM
            (Metta.Bindings.resolveAtomAux (.val key value :: source) fuel visited) =
              some values := by
          clear hresolve
          induction children generalizing values with
          | nil => simpa using hmap
          | cons head tail tailIH =>
            have hheadNot : key ∉ head.vars := by
              intro hin
              apply hnot
              simp [Metta.Atom.vars, hin]
            have htailNot : key ∉ (Metta.Atom.expr tail).vars := by
              intro hin
              apply hnot
              simpa [Metta.Atom.vars] using Or.inr hin
            simp only [List.mapM_cons] at hmap ⊢
            cases hhead : Metta.Bindings.resolveAtomAux source fuel visited head with
            | none => simp [hhead] at hmap
            | some headValue =>
              cases htail : tail.mapM (Metta.Bindings.resolveAtomAux source fuel visited) with
              | none => simp [hhead, htail] at hmap
              | some tailValues =>
                simp [hhead, htail] at hmap
                subst values
                rw [ih _ _ _ hheadNot hhead, tailIH htailNot tailValues htail]
                rfl
        simpa [hmap, hmap'] using hresolve

open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
  (ClosedValueBindings bindingValueKeys)

/-- Adding a fresh closed value cannot create a caller dependency cycle. -/
theorem hasLoop_false_of_cons_closed_fresh
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfresh : key ∉ Metta.Bindings.vars source) (hclosed : value.vars = [])
    (hloop : Metta.Bindings.hasLoop source = false) :
    Metta.Bindings.hasLoop (.val key value :: source) = false := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
  · have hdirect := (Bool.or_eq_false_iff.mp hloop).1
    rw [List.any_eq_false] at hdirect ⊢
    intro rel hrel
    rcases List.mem_cons.mp hrel with rfl | hrel
    · cases value with
      | var other => simp [Metta.Atom.vars] at hclosed
      | sym name => simp
      | gnd ground => simp
      | expr children => simp
    · have hr := hdirect rel hrel
      cases rel with
      | val name atom => cases atom <;> exact hr
      | eq left right => exact hr
  · intro other _
    by_cases heq : other = key
    · subst other
      have hclass : Metta.Bindings.eqClassOrdered (.val key value :: source) key = [key] := by
        rw [eqClassOrdered_cons_val]
        exact (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.outside_class hfresh).1
      have hvalues : Metta.Bindings.classValues (.val key value :: source) key = [value] := by
        simp [Metta.Bindings.classValues, hclass, Metta.Bindings.lookupVal]
      have hsize : value.size < (Metta.Bindings.resolutionFuel
          (.val key value :: source) (.var key)).pred := by
        simp [Metta.Bindings.resolutionFuel, Metta.Bindings.relationResolutionFuel,
          Metta.Atom.size]
        omega
      have hresolve :=
        Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolve_eq_closed_class_value
          hclass hvalues hclosed hsize
      exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_resolve_some hresolve
    · obtain ⟨resolved, hresolve⟩ :=
        Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_hasLoop_false
          hloop other
      have hforward := resolveAtomAux_cons_val_fresh value hfresh _ [] (.var other) resolved
        (by simp [Metta.Atom.vars, Ne.symm heq]) hresolve
      exact ⟨resolved, resolveAtomAux_some_at_resolutionFuel hforward⟩

/-- A normalized fresh closed-value prefix preserves native caller admission.
The caller may retain open values and equality relations. -/
theorem hasLoop_false_of_closed_prefix_fresh
    {source fresh : Metta.Bindings} (hclosed : ClosedValueBindings fresh)
    (hnodup : (bindingValueKeys fresh).Nodup)
    (hfresh : ∀ key ∈ bindingValueKeys fresh, key ∉ Metta.Bindings.vars source)
    (hloop : Metta.Bindings.hasLoop source = false) :
    Metta.Bindings.hasLoop (fresh ++ source) = false := by
  revert hnodup hfresh
  induction hclosed with
  | nil => intro _ _; exact hloop
  | @val key value rest hvalue hrest ih =>
    intro hnodup hfresh
    have hkeys : key ∉ bindingValueKeys rest ∧ (bindingValueKeys rest).Nodup := by
      simpa only [bindingValueKeys, List.nodup_cons] using hnodup
    have htailFresh : ∀ other ∈ bindingValueKeys rest,
        other ∉ Metta.Bindings.vars source := by
      intro other hother
      exact hfresh other (by simp [bindingValueKeys, hother])
    have hinner := ih hkeys.2 htailFresh
    have hkeyFresh : key ∉ Metta.Bindings.vars (rest ++ source) := by
      intro hin
      simp only [Metta.Bindings.vars, List.flatMap_append,
        List.mem_eraseDups, List.mem_append] at hin
      rcases hin with hin | hin
      · apply hkeys.1
        apply ClosedValueBindings.key_mem_of_vars_mem hrest
        simpa only [Metta.Bindings.vars, List.mem_eraseDups] using hin
      · exact hfresh key (by simp [bindingValueKeys])
          (by simpa only [Metta.Bindings.vars, List.mem_eraseDups] using hin)
    exact hasLoop_false_of_cons_closed_fresh hkeyFresh hvalue hinner

/-- A fresh value relation leaves every pre-existing caller read unchanged.
The inserted value may itself be open; its new key is not demanded here. -/
theorem instantiate_cons_val_fresh
    {source : Metta.Bindings} {key : String} (value atom : Metta.Atom)
    (hfresh : key ∉ Metta.Bindings.vars source)
    (hloop : Metta.Bindings.hasLoop source = false)
    (hnot : key ∉ atom.vars) :
    Metta.instantiate (.val key value :: source) atom = Metta.instantiate source atom := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.instantiate_eq_of_resolve_readout_on_vars
  intro other hother
  have hne : other ≠ key := by intro heq; subst other; exact hnot hother
  obtain ⟨resolved, hresolve⟩ :=
    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_hasLoop_false
      hloop other
  have hforward := resolveAtomAux_cons_val_fresh value hfresh _ [] (.var other) resolved
    (by simp [Metta.Atom.vars, Ne.symm hne]) hresolve
  have hcanonical := resolveAtomAux_some_at_resolutionFuel hforward
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom] using
    (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.instantiate_var_of_resolveAtomAux_some hcanonical).trans
      (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.instantiate_var_of_resolveAtomAux_some hresolve).symm

namespace FreshCallerControls

set_option maxRecDepth 8192

def caller : Metta.Bindings :=
  [.val "held" (.expr [.sym "f", .var "open"]), .eq "open" "same"]

def valuation (key : String) : Metta.Atom :=
  if key = "held" then .expr [.sym "f", .sym "seed"] else .sym "seed"

theorem caller_admitted : Metta.Bindings.hasLoop caller = false := by
  apply leaBindings_hasLoop_false_of_satisfied (valuation := valuation)
  · simp [LeaBindingSatisfied, caller, valuation, applyClassSolution]
  · simp [LeaAssignmentsNonVariable, caller]
  · simp [LeaEqualitiesIrreflexive, caller]

theorem closed_extension_admitted :
    Metta.Bindings.hasLoop (.val "local" (.sym "closed") :: caller) = false := by
  apply hasLoop_false_of_cons_closed_fresh
  · simp [caller, Metta.Bindings.vars, Metta.Atom.vars]
  · simp [Metta.Atom.vars]
  · exact caller_admitted

theorem existing_open_read_preserved :
    Metta.instantiate (.val "local" (.sym "closed") :: caller) (.var "held") =
      Metta.instantiate caller (.var "held") := by
  apply instantiate_cons_val_fresh
  · simp [caller, Metta.Bindings.vars, Metta.Atom.vars]
  · exact caller_admitted
  · simp [Metta.Atom.vars]

theorem open_self_extension_rejected :
    Metta.Bindings.hasLoop (.val "local" (.var "local") :: caller) = true := by
  simp [Metta.Bindings.hasLoop]

theorem new_key_read_changes :
    Metta.instantiate (.val "local" (.sym "closed") :: caller) (.var "local") ≠
      Metta.instantiate caller (.var "local") := by
  simp [caller, Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Bindings.resolve,
    Metta.Bindings.resolutionFuel, Metta.Bindings.relationResolutionFuel,
    Metta.Bindings.resolveAtomAux, Metta.Bindings.eqClassOrdered,
    Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
    Metta.Bindings.eqStep, Metta.Bindings.classValues, Metta.Bindings.lookupVal,
    Metta.Atom.size]

end FreshCallerControls

section ClosedQueryFrame

open Metta
open Metta.Minimal (Stack Item evalResult freshenRuleAvoiding)
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

theorem queryOp_closed_match_hasLoop_false
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom)
    (htarget : target.vars = []) (hcaller : Metta.Bindings.hasLoop caller = false)
    {matched : Metta.Bindings}
    (hmatched : matched ∈ Metta.matchAtoms
      (freshenRuleAvoiding counter (queryOpAvoid prev target caller) rule.1 rule.2).1.1 target) :
    Metta.Bindings.hasLoop (matched.reverse ++ caller) = false := by
  obtain ⟨hc, hn, hs⟩ := matchAtoms_closed_footprint _ _ _ htarget hmatched
  have hkeys := ValueBindings.bindingValueKeys_reverse hc.toValueBindings
  apply hasLoop_false_of_closed_prefix_fresh (ClosedValueBindings.reverse hc)
  · simpa only [hkeys, List.nodup_reverse] using hn
  · intro key hkey
    rw [hkeys, List.mem_reverse] at hkey
    exact queryOp_freshened_rule_avoids_caller prev target caller counter rule key
      (List.mem_append_left _ (hs key hkey))
  · exact hcaller

theorem queryOpItemsOfRule_closed_frame
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom)
    (htarget : target.vars = []) (hcaller : Metta.Bindings.hasLoop caller = false) :
    queryOpItemsOfRule prev target caller counter rule =
      (Metta.matchAtoms
        (freshenRuleAvoiding counter (queryOpAvoid prev target caller) rule.1 rule.2).1.1 target).map
        (fun matched => evalResult prev
          (instantiate matched
            (freshenRuleAvoiding counter (queryOpAvoid prev target caller) rule.1 rule.2).1.2)
          (matched.reverse ++ caller)) := by
  have hbody : ∀ key ∈
      (freshenRuleAvoiding counter (queryOpAvoid prev target caller) rule.1 rule.2).1.2.vars,
      key ∉ caller.vars := by
    intro key hkey
    exact queryOp_freshened_rule_avoids_caller prev target caller counter rule key
      (List.mem_append_right _ hkey)
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro matched hmatched
  obtain ⟨hc, hn, _⟩ := matchAtoms_closed_footprint _ _ _ htarget hmatched
  rw [queryOp_closed_match_merge prev target caller counter rule htarget hmatched]
  simp only [List.filterMap_cons, List.filterMap_nil]
  rw [queryOp_closed_match_hasLoop_false prev target caller counter rule htarget hcaller hmatched]
  simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, and_true]
  rw [instantiate_closed_fresh_caller (ClosedValueBindings.reverse hc) _ hbody,
    instantiate_reverse_closed_nodup hc hn]


end ClosedQueryFrame

/-! ## Composition: loop persistence for the raw value insertion -/

private theorem lookupVal_isSome_of_mem :
    ∀ {lb : Metta.Bindings} {y : String} {v : Metta.Atom},
      Metta.BindingRel.val y v ∈ lb →
      (Metta.Bindings.lookupVal lb y).isSome = true
  | [], _, _, h => absurd h (List.not_mem_nil)
  | .val z w :: rest, y, v, h => by
    simp only [Metta.Bindings.lookupVal]
    by_cases hyz : (y == z) = true
    · rw [if_pos hyz]; rfl
    · rw [if_neg hyz]
      cases List.mem_cons.mp h with
      | inl heq =>
        cases heq
        exact absurd (by simp) hyz
      | inr htail => exact lookupVal_isSome_of_mem htail
  | .eq _ _ :: rest, y, v, h => by
    simp only [Metta.Bindings.lookupVal]
    cases List.mem_cons.mp h with
    | inl heq => cases heq
    | inr htail => exact lookupVal_isSome_of_mem htail

private theorem mem_vars_cons
    {rel : Metta.BindingRel} {lb : Metta.Bindings} {x : String}
    (h : x ∈ Metta.Bindings.vars lb) :
    x ∈ Metta.Bindings.vars (rel :: lb) := by
  unfold Metta.Bindings.vars at h ⊢
  rw [List.mem_eraseDups] at h ⊢
  rw [List.flatMap_cons]
  exact List.mem_append_right _ h

/-- **Loop persistence, fresh value insertion.**  A loop-free raw value
insertion for a key whose class is valueless certifies a loop-free source:
the direct scan restricts to the sublist, and every recursive resolution
replays in the source and re-canonicalizes to the source's own budget. -/
theorem hasLoop_false_of_addValRaw_fresh
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (hfresh : Metta.Bindings.classValues source key = [])
    (hloop : (Metta.Bindings.addValRaw source key value).hasLoop = false) :
    source.hasLoop = false := by
  have hlookup : Metta.Bindings.lookupVal source key = none := by
    cases hl : Metta.Bindings.lookupVal source key with
    | none => rfl
    | some v =>
      exfalso
      have hmem : v ∈ Metta.Bindings.classValues source key := by
        unfold Metta.Bindings.classValues
        exact List.mem_filterMap.mpr
          ⟨key, self_mem_eqClassOrdered source key, hl⟩
      rw [hfresh] at hmem
      exact absurd hmem (List.not_mem_nil)
  have hremove : Metta.Bindings.removeVal source key = source := by
    unfold Metta.Bindings.removeVal
    apply List.filter_eq_self.mpr
    intro rel hrel
    cases rel with
    | eq _ _ => simp
    | val y v =>
      simp only []
      by_cases hy : y = key
      · subst hy
        have := lookupVal_isSome_of_mem hrel
        rw [hlookup] at this
        cases this
      · simpa using hy
  unfold Metta.Bindings.addValRaw at hloop
  rw [hremove] at hloop
  unfold Metta.Bindings.hasLoop at hloop ⊢
  rw [Bool.or_eq_false_iff] at hloop ⊢
  obtain ⟨hdirect, hrecursive⟩ := hloop
  constructor
  · simp only [List.any_cons, Bool.or_eq_false_iff] at hdirect
    exact hdirect.2
  · rw [List.any_eq_false] at hrecursive ⊢
    intro x hx
    have hx' := mem_vars_cons
      (rel := Metta.BindingRel.val key value) hx
    have hext := hrecursive x hx'
    cases hres : Metta.Bindings.resolveAtomAux
        (Metta.BindingRel.val key value :: source)
        (Metta.Bindings.resolutionFuel
          (Metta.BindingRel.val key value :: source) (Metta.Atom.var x))
        [] (Metta.Atom.var x) with
    | none => rw [hres] at hext; exact absurd rfl hext
    | some r =>
      have hsome := resolveAtomAux_some_of_cons_val_fresh hfresh
        _ _ _ _ hres
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
      have hcanon := resolveAtomAux_some_at_resolutionFuel hr'
      simp [hcanon]

/-! ## Invariance and transfer under an equality cons -/

section ConsEq

variable (source : Metta.Bindings) (l r : String)

private theorem lookupVal_cons_eq (z : String) :
    Metta.Bindings.lookupVal (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.lookupVal source z := rfl

private theorem leaEqualityEdges_cons_eq :
    leaEqualityEdges (Metta.BindingRel.eq l r :: source) =
      (l, r) :: leaEqualityEdges source := rfl

private theorem edgeGraph_le_cons_eq :
    EqualityClosure.edgeGraph (leaEqualityEdges source) ≤
      EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source)) := by
  intro u v huv
  rw [EqualityClosure.edgeGraph_adj_iff] at huv ⊢
  refine ⟨huv.1, ?_⟩
  rw [leaEqualityEdges_cons_eq]
  rcases huv.2 with h | h
  · exact Or.inl (List.mem_cons_of_mem _ h)
  · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem eqClass_mem_mono_cons_eq {z w : String}
    (h : w ∈ Metta.Bindings.eqClass source z) :
    w ∈ Metta.Bindings.eqClass (Metta.BindingRel.eq l r :: source) z := by
  rw [mem_leaEqClass_iff_reachable] at h ⊢
  exact h.mono (edgeGraph_le_cons_eq source l r)

private theorem reachable_cons_eq_untouched {z w : String}
    (hz : ¬ (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z l)
    (h : (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z w) :
    (EqualityClosure.edgeGraph (leaEqualityEdges source)).Reachable z w := by
  suffices key : ∀ (a b : String),
      (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Walk a b →
      ¬ (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
          a l →
      (EqualityClosure.edgeGraph (leaEqualityEdges source)).Reachable a b by
    exact h.elim fun walk => key z w walk hz
  intro a b walk
  induction walk with
  | nil => intro _; exact .rfl
  | @cons start next finish hadj tail ih =>
    intro hstart
    have hnext : ¬ (EqualityClosure.edgeGraph
        (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
          next l :=
      fun hcontra => hstart (hadj.reachable.trans hcontra)
    have hadjSource : (EqualityClosure.edgeGraph
        (leaEqualityEdges source)).Adj start next := by
      have hadjOrig := hadj
      rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
      refine ⟨hadj.1, ?_⟩
      rw [leaEqualityEdges_cons_eq] at hadj
      rcases hadj.2 with h' | h'
      · rcases List.mem_cons.mp h' with heq | hmem
        · exfalso
          have : start = l := congrArg Prod.fst heq
          subst this
          exact hstart .rfl
        · exact Or.inl hmem
      · rcases List.mem_cons.mp h' with heq | hmem
        · exfalso
          have hnextl : next = l := congrArg Prod.fst heq
          subst hnextl
          exact hstart hadjOrig.reachable
        · exact Or.inr hmem
    exact hadjSource.reachable.trans (ih hnext)

private theorem mem_eqVarsInOrder_cons_eq {v : String}
    (hv : v ∈ Metta.Bindings.eqVarsInOrder source) :
    v ∈ Metta.Bindings.eqVarsInOrder
      (Metta.BindingRel.eq l r :: source) := by
  rw [leaEqVarsInOrder_cons_eq]
  simp only []
  split <;> split <;>
    first
      | exact hv
      | exact List.mem_append_left _ hv
      | exact List.mem_append_left _ (List.mem_append_left _ hv)

private theorem filter_eqVarsInOrder_cons_eq {p : String → Bool}
    (hl : p l = false) (hr : p r = false) :
    (Metta.Bindings.eqVarsInOrder
        (Metta.BindingRel.eq l r :: source)).filter p =
      (Metta.Bindings.eqVarsInOrder source).filter p := by
  rw [leaEqVarsInOrder_cons_eq]
  simp only []
  split <;> split <;> simp [List.filter_append, hl, hr]

private theorem mem_eqClassOrdered_cons_eq {z y : String}
    (hy : y ∈ Metta.Bindings.eqClassOrdered source z) :
    y ∈ Metta.Bindings.eqClassOrdered
      (Metta.BindingRel.eq l r :: source) z := by
  rcases mem_eqClassOrdered_cases' hy with heq | hclass
  · subst heq
    exact self_mem_eqClassOrdered _ _
  · by_cases hyz : y = z
    · subst hyz
      exact self_mem_eqClassOrdered _ _
    · have hyorder : y ∈ Metta.Bindings.eqVarsInOrder source :=
        mem_eqVarsInOrder_of_reachable_ne hyz
          (mem_leaEqClass_iff_reachable.mp hclass).symm
      have hyorderE : y ∈ Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source) :=
        mem_eqVarsInOrder_cons_eq source l r hyorder
      have hyclassE : y ∈ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z :=
        eqClass_mem_mono_cons_eq source l r hclass
      have hyf : y ∈ (Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source)).filter
          (fun w => (Metta.Bindings.eqClass
            (Metta.BindingRel.eq l r :: source) z).contains w) :=
        List.mem_filter.mpr ⟨hyorderE, by simpa using hyclassE⟩
      unfold Metta.Bindings.eqClassOrdered
      cases hfilter : (Metta.Bindings.eqVarsInOrder
          (Metta.BindingRel.eq l r :: source)).filter
          (fun w => (Metta.Bindings.eqClass
            (Metta.BindingRel.eq l r :: source) z).contains w) with
      | nil =>
        rw [hfilter] at hyf
        exact absurd hyf (List.not_mem_nil)
      | cons c cs =>
        rw [hfilter] at hyf
        try rw [hfilter]
        exact hyf

private theorem mem_classValues_cons_eq {z : String} {v : Metta.Atom}
    (hv : v ∈ Metta.Bindings.classValues source z) :
    v ∈ Metta.Bindings.classValues
      (Metta.BindingRel.eq l r :: source) z := by
  unfold Metta.Bindings.classValues at hv ⊢
  obtain ⟨y, hy, hlookup⟩ := List.mem_filterMap.mp hv
  exact List.mem_filterMap.mpr
    ⟨y, mem_eqClassOrdered_cons_eq source l r hy,
      by rw [lookupVal_cons_eq]; exact hlookup⟩

private theorem eqClassOrdered_cons_eq_untouched {z : String}
    (hlr : l ≠ r)
    (htouched : l ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z) :
    Metta.Bindings.eqClassOrdered (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.eqClassOrdered source z := by
  have hzl : ¬ (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Reachable
        z l := fun hcontra =>
    htouched (mem_leaEqClass_iff_reachable.mpr hcontra)
  have hadjrl : (EqualityClosure.edgeGraph
      (leaEqualityEdges (Metta.BindingRel.eq l r :: source))).Adj r l := by
    rw [EqualityClosure.edgeGraph_adj_iff]
    exact ⟨fun hcontra => hlr hcontra.symm, by
      rw [leaEqualityEdges_cons_eq]
      exact Or.inr List.mem_cons_self⟩
  have hrtouched : r ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z := by
    intro hcontra
    exact hzl ((mem_leaEqClass_iff_reachable.mp hcontra).trans
      hadjrl.reachable)
  have hlcontains : ((Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z).contains l) = false := by
    simpa using htouched
  have hrcontains : ((Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z).contains r) = false := by
    simpa using hrtouched
  unfold Metta.Bindings.eqClassOrdered
  rw [filter_eqVarsInOrder_cons_eq source l r hlcontains hrcontains]
  have hpred : (Metta.Bindings.eqVarsInOrder source).filter
      (fun w => (Metta.Bindings.eqClass
        (Metta.BindingRel.eq l r :: source) z).contains w) =
      (Metta.Bindings.eqVarsInOrder source).filter
        (fun w => (Metta.Bindings.eqClass source z).contains w) := by
    apply List.filter_congr
    intro w _
    by_cases hw : w ∈ Metta.Bindings.eqClass source z
    · have hwE : w ∈ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z :=
        eqClass_mem_mono_cons_eq source l r hw
      simp [hw, hwE]
    · have hwE : w ∉ Metta.Bindings.eqClass
          (Metta.BindingRel.eq l r :: source) z := by
        intro hcontra
        apply hw
        rw [mem_leaEqClass_iff_reachable]
        exact reachable_cons_eq_untouched source l r hzl
          (mem_leaEqClass_iff_reachable.mp hcontra)
      simp [hw, hwE]
  rw [hpred]

private theorem classValues_cons_eq_untouched {z : String}
    (hlr : l ≠ r)
    (htouched : l ∉ Metta.Bindings.eqClass
      (Metta.BindingRel.eq l r :: source) z) :
    Metta.Bindings.classValues (Metta.BindingRel.eq l r :: source) z =
      Metta.Bindings.classValues source z := by
  unfold Metta.Bindings.classValues
  rw [eqClassOrdered_cons_eq_untouched source l r hlr htouched]
  apply List.filterMap_congr
  intro w _
  rw [lookupVal_cons_eq]

private theorem classValues_congr_of_ordered_eq
    {lb : Metta.Bindings} {a b : String}
    (h : Metta.Bindings.eqClassOrdered lb a =
      Metta.Bindings.eqClassOrdered lb b) :
    Metta.Bindings.classValues lb a = Metta.Bindings.classValues lb b := by
  unfold Metta.Bindings.classValues
  rw [h]

private theorem classValues_head_nonvar
    {lb : Metta.Bindings}
    (hnonvar : LeaAssignmentsNonVariable lb) {z : String}
    {v : Metta.Atom} (hv : v ∈ Metta.Bindings.classValues lb z) :
    ∀ y, v ≠ Metta.Atom.var y := by
  intro y hcontra
  subst hcontra
  unfold Metta.Bindings.classValues at hv
  obtain ⟨w, _, hlookup⟩ := List.mem_filterMap.mp hv
  exact hnonvar w y (lookupVal_mem' hlookup)

end ConsEq

/-! ## Success replay: extended equality record to source -/

private theorem resolveAtomAux_some_of_cons_eq
    {source : Metta.Bindings} {l r : String}
    (hlr : l ≠ r)
    (hnonvar : LeaAssignmentsNonVariable source)
    (hsame : ∀ v ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq l r :: source) l,
      ∀ w ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq l r :: source) l, v = w) :
    ∀ (fuel : Nat) (visitedE visitedS : List String) (a res : Metta.Atom),
      (∀ s ∈ visitedS, s ∈ visitedE) →
      Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq l r :: source) fuel visitedE a = some res →
      (Metta.Bindings.resolveAtomAux source fuel visitedS a).isSome =
        true := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _ _ _ h
    simp [Metta.Bindings.resolveAtomAux] at h
  | succ fuel ih =>
    intro visitedE visitedS a res hvis h
    cases a with
    | sym s => simp [Metta.Bindings.resolveAtomAux]
    | gnd g => simp [Metta.Bindings.resolveAtomAux]
    | expr xs =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      cases hmap : xs.mapM (Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq l r :: source) fuel visitedE) with
      | none => rw [hmap] at h; cases h
      | some ys =>
        obtain ⟨ws, hws⟩ := mapM_some_of_pointwise xs ys hmap
          (fun z _ w hw => ih visitedE visitedS z w hvis hw)
        rw [hws]
        simp
    | var z =>
      simp only [Metta.Bindings.resolveAtomAux] at h ⊢
      by_cases hgS : ((Metta.Bindings.eqClassOrdered source z).any
          visitedS.contains) = true
      · exfalso
        rw [List.any_eq_true] at hgS
        obtain ⟨w, hw, hwv⟩ := hgS
        have hgE : ((Metta.Bindings.eqClassOrdered
            (Metta.BindingRel.eq l r :: source) z).any
            visitedE.contains) = true := by
          rw [List.any_eq_true]
          refine ⟨w, mem_eqClassOrdered_cons_eq source l r hw, ?_⟩
          have hwS : w ∈ visitedS := by simpa using hwv
          simpa using hvis w hwS
        rw [if_pos hgE] at h
        cases h
      · rw [if_neg hgS]
        by_cases hgE : ((Metta.Bindings.eqClassOrdered
            (Metta.BindingRel.eq l r :: source) z).any
            visitedE.contains) = true
        · rw [if_pos hgE] at h
          cases h
        · rw [if_neg hgE] at h
          have hvisJump : ∀ s ∈ Metta.Bindings.eqClassOrdered source z ++
              visitedS, s ∈ Metta.Bindings.eqClassOrdered
                (Metta.BindingRel.eq l r :: source) z ++ visitedE := by
            intro s hs
            rcases List.mem_append.mp hs with hs | hs
            · exact List.mem_append_left _
                (mem_eqClassOrdered_cons_eq source l r hs)
            · exact List.mem_append_right _ (hvis s hs)
          cases hvaluesS : Metta.Bindings.classValues source z with
          | nil => simp
          | cons v rest =>
            have hvmem : v ∈ Metta.Bindings.classValues source z := by
              rw [hvaluesS]; exact List.mem_cons_self
            have hvnonvar := classValues_head_nonvar hnonvar hvmem
            have hjump : Metta.Bindings.resolveAtomAux
                (Metta.BindingRel.eq l r :: source) fuel
                (Metta.Bindings.eqClassOrdered
                  (Metta.BindingRel.eq l r :: source) z ++ visitedE) v =
                some res := by
              by_cases htouched : l ∈ Metta.Bindings.eqClass
                  (Metta.BindingRel.eq l r :: source) z
              · have hordered : Metta.Bindings.eqClassOrdered
                    (Metta.BindingRel.eq l r :: source) l =
                    Metta.Bindings.eqClassOrdered
                      (Metta.BindingRel.eq l r :: source) z :=
                  eqClassOrdered_congr_of_mem htouched
                have hclassvals : Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) l =
                    Metta.Bindings.classValues
                      (Metta.BindingRel.eq l r :: source) z :=
                  classValues_congr_of_ordered_eq hordered
                have hvE : v ∈ Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) z :=
                  mem_classValues_cons_eq source l r hvmem
                cases hvaluesE : Metta.Bindings.classValues
                    (Metta.BindingRel.eq l r :: source) z with
                | nil =>
                  rw [hvaluesE] at hvE
                  exact absurd hvE (List.not_mem_nil)
                | cons vE restE =>
                  have hvEhead : vE ∈ Metta.Bindings.classValues
                      (Metta.BindingRel.eq l r :: source) z := by
                    rw [hvaluesE]; exact List.mem_cons_self
                  have hveq : v = vE := by
                    apply hsame
                    · rw [hclassvals]; exact hvE
                    · rw [hclassvals]; exact hvEhead
                  rw [hvaluesE] at h
                  subst hveq
                  cases v with
                  | var y => exact absurd rfl (hvnonvar y)
                  | sym s => simpa using h
                  | gnd g => simpa using h
                  | expr atoms => simpa using h
              · have hclassvals := classValues_cons_eq_untouched
                  source l r hlr htouched
                rw [hclassvals, hvaluesS] at h
                cases v with
                | var y => exact absurd rfl (hvnonvar y)
                | sym s => simpa using h
                | gnd g => simpa using h
                | expr atoms => simpa using h
            cases v with
            | var y => exact absurd rfl (hvnonvar y)
            | sym s => simpa using ih _ _ _ _ hvisJump hjump
            | gnd g => simpa using ih _ _ _ _ hvisJump hjump
            | expr atoms => simpa using ih _ _ _ _ hvisJump hjump

/-! ## Pairwise-equal class values from an empty unifier -/

private theorem applyClassSolution_id :
    ∀ a : Metta.Atom,
      applyClassSolution (fun x => Metta.Atom.var x) a = a := by
  suffices key : ∀ (n : Nat) (a : Metta.Atom), a.size ≤ n →
      applyClassSolution (fun x => Metta.Atom.var x) a = a by
    exact fun a => key a.size a le_rfl
  intro n
  induction n with
  | zero =>
    intro a hsize
    exact absurd hsize (by have := persist_size_pos a; omega)
  | succ n ihn =>
    intro a hsize
    cases a with
    | sym s => simp [applyClassSolution]
    | gnd g => simp [applyClassSolution]
    | var v => simp [applyClassSolution]
    | expr atoms =>
      simp only [applyClassSolution, Metta.Atom.expr.injEq]
      have : atoms.map (applyClassSolution (fun x => Metta.Atom.var x)) =
          atoms.map id := by
        apply List.map_congr_left
        intro child hchild
        have := persist_size_lt_of_mem hchild
        exact ihn child (by omega)
      rw [this, List.map_id]

private theorem classValues_pairwise_of_unifyValues_nil
    {lb : Metta.Bindings} {z : String}
    (hnoFloat : ∀ v ∈ Metta.Bindings.classValues lb z,
      MettaAtomNoFloat v)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues lb z) = some []) :
    ∀ v ∈ Metta.Bindings.classValues lb z,
      ∀ w ∈ Metta.Bindings.classValues lb z, v = w := by
  have hiff := unifyValues_solution_iff
    (fun x => Metta.Atom.var x) hnoFloat hunify
  have hsat : MettaEquationsSatisfied (fun x => Metta.Atom.var x)
      (mettaClassValueEquations (Metta.Bindings.classValues lb z)) :=
    hiff.mp (fun c hc => absurd hc (List.not_mem_nil))
  cases hvals : Metta.Bindings.classValues lb z with
  | nil =>
    intro v hv
    exact absurd hv (List.not_mem_nil)
  | cons first rest =>
    rw [hvals] at hsat
    have hhead : ∀ v ∈ first :: rest, v = first := by
      intro v hv
      rcases List.mem_cons.mp hv with heq | hmem
      · exact heq
      · have hpair : MettaEquationSatisfied (fun x => Metta.Atom.var x)
            (first, v) := by
          apply hsat
          simp only [mettaClassValueEquations]
          exact List.mem_map.mpr ⟨v, hmem, rfl⟩
        have := hpair
        simp only [MettaEquationSatisfied, applyClassSolution_id] at this
        exact this.symm
    intro v hv w hw
    rw [hhead v hv, hhead w hw]

/-! ## Composition: loop persistence for the raw equality insertion -/

/-- **Loop persistence, raw equality insertion with an empty class
unifier.**  A loop-free `addEqRaw source left right` whose joined class
carries an empty value unifier certifies a loop-free `source`. -/
theorem hasLoop_false_of_addEqRaw_emptyUnifier
    {source : Metta.Bindings} {left right : String}
    (hnonvar : LeaAssignmentsNonVariable source)
    (hnoFloat : LeaBindingsNoFloat source)
    (hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw source left right) left) = some [])
    (hloop : (Metta.Bindings.addEqRaw source left right).hasLoop = false) :
    source.hasLoop = false := by
  by_cases hlr : (left == right) = true
  · unfold Metta.Bindings.addEqRaw at hloop
    rw [if_pos hlr] at hloop
    exact hloop
  · have hlr' : left ≠ right := by simpa using hlr
    have hext : Metta.Bindings.addEqRaw source left right =
        Metta.BindingRel.eq left right :: source := by
      unfold Metta.Bindings.addEqRaw
      rw [if_neg hlr]
    rw [hext] at hloop hunify
    have hnoFloatVals : ∀ v ∈ Metta.Bindings.classValues
        (Metta.BindingRel.eq left right :: source) left,
        MettaAtomNoFloat v := by
      intro v hv
      unfold Metta.Bindings.classValues at hv
      obtain ⟨y, _, hlookup⟩ := List.mem_filterMap.mp hv
      have hval := lookupVal_mem' hlookup
      rcases List.mem_cons.mp hval with heq | hmem
      · cases heq
      · exact hnoFloat y v hmem
    have hsame := classValues_pairwise_of_unifyValues_nil
      hnoFloatVals hunify
    unfold Metta.Bindings.hasLoop at hloop ⊢
    rw [Bool.or_eq_false_iff] at hloop ⊢
    obtain ⟨hdirect, hrecursive⟩ := hloop
    constructor
    · simp only [List.any_cons, Bool.or_eq_false_iff] at hdirect
      exact hdirect.2
    · rw [List.any_eq_false] at hrecursive ⊢
      intro x hx
      have hx' := mem_vars_cons
        (rel := Metta.BindingRel.eq left right) hx
      have hext' := hrecursive x hx'
      cases hres : Metta.Bindings.resolveAtomAux
          (Metta.BindingRel.eq left right :: source)
          (Metta.Bindings.resolutionFuel
            (Metta.BindingRel.eq left right :: source) (Metta.Atom.var x))
          [] (Metta.Atom.var x) with
      | none => rw [hres] at hext'; exact absurd rfl hext'
      | some res =>
        have hsome := resolveAtomAux_some_of_cons_eq hlr' hnonvar hsame
          _ _ [] _ _ (fun s hs => hs) hres
        obtain ⟨res', hres'⟩ := Option.isSome_iff_exists.mp hsome
        have hcanon := resolveAtomAux_some_at_resolutionFuel hres'
        simp [hcanon]

/-! ## Fresh frame reflection and accepted query callers -/

open Metta
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
  (ClosedValueBindings bindingValueKeys)

/-- Removing a value at a globally fresh key cannot conceal an old cycle. -/
theorem hasLoop_false_of_cons_val_outside
    {source : Metta.Bindings} {key : String} {value : Metta.Atom}
    (fresh : key ∉ Metta.Bindings.vars source)
    (safe : Metta.Bindings.hasLoop (.val key value :: source) = false) :
    Metta.Bindings.hasLoop source = false := by
  have values : Metta.Bindings.classValues source key = [] :=
    (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.outside_class
      (b := source) fresh).2
  have remove : Metta.Bindings.removeVal source key = source :=
    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.removeVal_not_mem_eq_self
      (fun member => fresh
        (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.bindingValueKey_mem_vars member))
  exact hasLoop_false_of_addValRaw_fresh (source := source) (key := key) (value := value)
    values (by simpa only [Metta.Bindings.addValRaw, remove] using safe)

/-- A fresh closed-value frame preserves and reflects caller loop admission. -/
theorem hasLoop_false_iff_closed_prefix_fresh
    {source added : Metta.Bindings} (closed : ClosedValueBindings added)
    (unique : (bindingValueKeys added).Nodup)
    (fresh : ∀ key ∈ bindingValueKeys added, key ∉ Metta.Bindings.vars source) :
    Metta.Bindings.hasLoop (added ++ source) = false ↔
      Metta.Bindings.hasLoop source = false := by
  constructor
  · revert unique fresh
    induction closed with
    | nil => intro _ _ safe; exact safe
    | @val key value rest valueClosed restClosed ih =>
      intro unique fresh safe
      have keys : key ∉ bindingValueKeys rest ∧ (bindingValueKeys rest).Nodup := by
        simpa only [bindingValueKeys, List.nodup_cons] using unique
      have tailFresh : ∀ other ∈ bindingValueKeys rest,
          other ∉ Metta.Bindings.vars source := by
        intro other member
        exact fresh other (by simp [bindingValueKeys, member])
      have keyFresh : key ∉ Metta.Bindings.vars (rest ++ source) := by
        intro member
        simp only [Metta.Bindings.vars, List.flatMap_append,
          List.mem_eraseDups, List.mem_append] at member
        rcases member with member | member
        · apply keys.1
          exact ClosedValueBindings.key_mem_of_vars_mem restClosed
            (by simpa only [Metta.Bindings.vars, List.mem_eraseDups] using member)
        · exact fresh key (by simp [bindingValueKeys])
            (by simpa only [Metta.Bindings.vars, List.mem_eraseDups] using member)
      exact ih keys.2 tailFresh (hasLoop_false_of_cons_val_outside keyFresh safe)
  · exact hasLoop_false_of_closed_prefix_fresh closed unique fresh

open Metta.Minimal (Stack Item freshenRuleAvoiding)
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-- An accepted closed query candidate reflects caller admission. Fresh rule
variables cannot conceal an existing caller cycle. -/
theorem queryOpItemsOfRule_closed_caller_admitted
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom) (closed : target.vars = [])
    (item : Item) (present : item ∈ queryOpItemsOfRule prev target caller counter rule) :
    Metta.Bindings.hasLoop caller = false := by
  obtain ⟨matched, member, safe, _⟩ :=
    (mem_queryOpItemsOfRule_closed_frame_iff prev target caller counter rule closed item).mp present
  obtain ⟨values, unique, keys⟩ := matchAtoms_closed_footprint _ _ _ closed member
  have reversed := ValueBindings.bindingValueKeys_reverse values.toValueBindings
  apply (hasLoop_false_iff_closed_prefix_fresh (ClosedValueBindings.reverse values) ?_ ?_).mp safe
  · simpa only [reversed, List.nodup_reverse] using unique
  · intro key member
    rw [reversed, List.mem_reverse] at member
    exact queryOp_freshened_rule_avoids_caller prev target caller counter rule key
      (List.mem_append_left _ (keys key member))

theorem queryOpItemsOfRule_closed_cyclic_caller
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom) (closed : target.vars = [])
    (cyclic : Metta.Bindings.hasLoop caller = true) :
    queryOpItemsOfRule prev target caller counter rule = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro item present
  have safe := queryOpItemsOfRule_closed_caller_admitted prev target caller counter rule closed item present
  rw [cyclic] at safe
  cases safe


open Metta.Minimal (unifyOp finItem)

/-- A closed target matched against a variable has one concrete binding row. -/
theorem matchAtoms_closed_variable (value : Metta.Atom) (key : VarName)
    (closed : value.vars = []) :
    Metta.matchAtoms value (.var key) = [[.val key value]] := by
  have occurs := occurs_eq_false_of_not_mem_vars key value (by rw [closed]; simp)
  have loop := hasLoop_singleton_val_closed_false key value closed
  cases value with
  | var other => simp [Metta.Atom.vars] at closed
  | sym symbol => simp [Metta.matchAtoms, Metta.matchAtomsWith, occurs, loop]
  | gnd ground => simp [Metta.matchAtoms, Metta.matchAtomsWith, occurs, loop]
  | expr children => simp [Metta.matchAtoms, Metta.matchAtomsWith, occurs, loop]

/-! ## Closed assignments to valueless equality classes -/

theorem classValues_cons_val_of_valueless
    {caller : Metta.Bindings} {key : VarName} (value : Metta.Atom)
    (valueless : Metta.Bindings.classValues caller key = []) :
    ∃ rest, Metta.Bindings.classValues (.val key value :: caller) key = value :: rest := by
  have present : value ∈ Metta.Bindings.classValues (.val key value :: caller) key := by
    apply leaClassValue_mem_iff.mpr
    exact ⟨key, mem_leaEqClass_iff_reachable.mpr .rfl, by simp [Metta.Bindings.lookupVal]⟩
  have unique : ∀ candidate ∈ Metta.Bindings.classValues (.val key value :: caller) key,
      candidate = value := by
    intro candidate member
    obtain ⟨owner, inClass, selected⟩ := List.mem_filterMap.mp member
    rw [eqClassOrdered_cons_val] at inClass
    by_cases same : owner = key
    · subst owner
      simpa only [Metta.Bindings.lookupVal, beq_self_eq_true, ↓reduceIte,
        Option.some.injEq] using selected.symm
    · have absent : Metta.Bindings.lookupVal caller owner = none :=
        List.filterMap_eq_nil_iff.mp valueless owner inClass
      simp [Metta.Bindings.lookupVal, same, absent] at selected
  cases values : Metta.Bindings.classValues (.val key value :: caller) key with
  | nil => simp [values] at present
  | cons first rest =>
      have same := unique first (by rw [values]; simp)
      subst first
      exact ⟨rest, rfl⟩

theorem instantiate_cons_valueless_closed
    {caller : Metta.Bindings} {key : VarName} {value : Metta.Atom}
    (valueless : Metta.Bindings.classValues caller key = [])
    (closed : value.vars = [])
    (admitted : Metta.Bindings.hasLoop (.val key value :: caller) = false) :
    Metta.instantiate (.val key value :: caller) (.var key) = value := by
  obtain ⟨rest, values⟩ := classValues_cons_val_of_valueless value valueless
  rw [Bindings.instantiate_first_class_value admitted values
    (by intro other equal; subst value; simp [Metta.Atom.vars] at closed)]
  exact instantiate_of_closed _ _ closed

theorem addVarBinding_closed_valueless
    (caller : Metta.Bindings) (key : VarName) (value : Metta.Atom)
    (closed : value.vars = [])
    (valueless : Metta.Bindings.classValues caller key = []) :
    Metta.Bindings.addVarBinding caller key value = [.val key value :: caller] := by
  have noKey : ∀ atom, Metta.BindingRel.val key atom ∉ caller := by
    have absent : Metta.Bindings.lookupVal caller key = none := by
      apply List.filterMap_eq_nil_iff.mp valueless key
      exact mem_leaEqClassOrdered_iff.mpr (mem_leaEqClass_iff_reachable.mpr .rfl)
    clear valueless
    induction caller with
    | nil => simp
    | cons relation rest ih =>
      cases relation with
      | eq left right =>
          exact fun atom member => (ih absent atom) (by simpa using member)
      | val other stored =>
          by_cases same : key = other
          · simp [Metta.Bindings.lookupVal, same] at absent
          · have tail : Metta.Bindings.lookupVal rest key = none := by
              simpa [Metta.Bindings.lookupVal, same] using absent
            intro atom member
            rcases List.mem_cons.mp member with equal | later
            · cases equal
              exact same rfl
            · exact ih tail atom later
  have unchanged : Metta.Bindings.removeVal caller key = caller := by
    apply List.filter_eq_self.mpr
    intro relation member
    cases relation with
    | eq left right => rfl
    | val other stored =>
        have different : other ≠ key := by
          intro same
          subst other
          exact noKey stored member
        simp [different]
  cases value with
  | var other => simp [Metta.Atom.vars] at closed
  | sym symbol | gnd ground | expr children =>
      simp only [Metta.Bindings.addVarBinding, valueless, Metta.Bindings.addValRaw, unchanged]

/-- A closed assignment to a valueless equality class retains its full caller.
The real post-assignment loop verdict still selects success or refusal. -/
theorem unifyOp_closed_valueless_class
    (prev : Stack) (value template otherwise : Metta.Atom)
    (caller : Metta.Bindings) (key : VarName)
    (closed : value.vars = [])
    (valueless : Metta.Bindings.classValues caller key = []) :
    unifyOp prev value (.var key) template otherwise caller =
      if Metta.Bindings.hasLoop (.val key value :: caller) then
        [finItem prev otherwise caller]
      else [finItem prev (Metta.instantiate (.val key value :: caller) template)
        (.val key value :: caller)] := by
  have matched := matchAtoms_closed_variable value key closed
  have merged : Metta.Bindings.merge caller [.val key value] = [.val key value :: caller] := by
    simpa only [Metta.Bindings.merge, List.foldl_cons, List.foldl_nil,
      Metta.Bindings.mergeOne, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
      addVarBinding_closed_valueless caller key value closed valueless
  cases loop : Metta.Bindings.hasLoop (.val key value :: caller) <;>
    simp [unifyOp, matched, merged, loop]


/-- A template depending only on the newly assigned class reads the supplied
closed value, while the complete caller and class aliases remain retained. -/
theorem unifyOp_closed_valueless_class_template
    (prev : Stack) (value template otherwise : Metta.Atom)
    (caller : Metta.Bindings) (key : VarName)
    (closed : value.vars = [])
    (valueless : Metta.Bindings.classValues caller key = [])
    (covered : ∀ name ∈ template.vars, name = key) :
    unifyOp prev value (.var key) template otherwise caller =
      if Metta.Bindings.hasLoop (.val key value :: caller) then
        [finItem prev otherwise caller]
      else [finItem prev (Metta.instantiate [.val key value] template)
        (.val key value :: caller)] := by
  rw [unifyOp_closed_valueless_class prev value template otherwise caller key closed valueless]
  cases loop : Metta.Bindings.hasLoop (.val key value :: caller) with
  | true => rfl
  | false =>
      have readout : Metta.instantiate (.val key value :: caller) template =
          Metta.instantiate [.val key value] template := by
        apply instantiate_eq_of_resolve_readout_on_vars
        intro name member
        rw [covered name member]
        have pointReadout : Metta.instantiate (.val key value :: caller) (.var key) =
            Metta.instantiate [.val key value] (.var key) := by
          rw [instantiate_cons_valueless_closed valueless closed loop,
            instantiate_singleton_val_var key value (by rw [closed]; simp)]
        simpa only [Metta.instantiate, Metta.Bindings.resolveAtom] using pointReadout
      rw [readout]

/-- Binding a fresh local to a closed value extends the actual caller record.
Neither its aliases nor its unrelated open values are reconstructed. -/
theorem unifyOp_closed_fresh_binder
    (prev : Stack) (value template otherwise : Metta.Atom)
    (caller : Metta.Bindings) (key : VarName)
    (closed : value.vars = []) (fresh : key ∉ caller.vars)
    (admitted : caller.hasLoop = false) :
    unifyOp prev value (.var key) template otherwise caller =
      [finItem prev (Metta.instantiate (.val key value :: caller) template)
        (.val key value :: caller)] := by
  have loop := hasLoop_false_of_cons_closed_fresh fresh closed admitted
  simpa only [loop, Bool.false_eq_true, ↓reduceIte] using
    unifyOp_closed_valueless_class prev value template otherwise caller key closed
      (Bindings.outside_class fresh).2

/-- A fresh closed local preserves admission in both directions. A cyclic
caller cannot acquire a successful branch merely by introducing a new name. -/
theorem unifyOp_closed_fresh_binder_cyclic
    (prev : Stack) (value template otherwise : Metta.Atom)
    (caller : Metta.Bindings) (key : VarName)
    (closed : value.vars = []) (fresh : key ∉ caller.vars)
    (cyclic : caller.hasLoop = true) :
    unifyOp prev value (.var key) template otherwise caller =
      [finItem prev otherwise caller] := by
  have loop : Metta.Bindings.hasLoop (.val key value :: caller) = true := by
    cases h : Metta.Bindings.hasLoop (.val key value :: caller) with
    | true => rfl
    | false =>
        have source := hasLoop_false_of_cons_val_outside fresh h
        rw [cyclic] at source
        cases source
  simpa only [loop, ↓reduceIte] using
    unifyOp_closed_valueless_class prev value template otherwise caller key closed
      (Bindings.outside_class fresh).2

/-- A template whose only free name is the introduced local has a caller-
independent value, while the resulting binding record still retains the caller. -/
theorem unifyOp_closed_fresh_binder_template
    (prev : Stack) (value template otherwise : Metta.Atom)
    (caller : Metta.Bindings) (key : VarName)
    (closed : value.vars = []) (fresh : key ∉ caller.vars)
    (admitted : caller.hasLoop = false)
    (covered : ∀ name ∈ template.vars, name = key) :
    unifyOp prev value (.var key) template otherwise caller =
      [finItem prev (Metta.instantiate [.val key value] template)
        (.val key value :: caller)] := by
  have loop := hasLoop_false_of_cons_closed_fresh fresh closed admitted
  simpa only [loop, Bool.false_eq_true, ↓reduceIte] using
    unifyOp_closed_valueless_class_template prev value template otherwise caller key
      closed (Bindings.outside_class fresh).2 covered

section ClosedSourceObservations

open Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Every original source match becomes one scoped candidate occurrence. Its
value is renamed only for still-unbound rule variables; its caller is retained. -/
theorem queryOpItemsOfRule_closed_source_map
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom) (htarget : target.vars = [])
    (hcaller : Metta.Bindings.hasLoop caller = false) :
    ∃ f : VarName → VarName, Function.Injective f ∧
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid prev target caller) rule.1 rule.2).1 =
        (renBy f rule.1,renBy f rule.2) ∧
      Metta.Minimal.queryOpItemsOfRule prev target caller counter rule =
        (Metta.matchAtoms rule.1 target).map (fun source =>
          evalResult prev (renBy f (Metta.instantiate source rule.2))
            ((renameBindings f source).reverse ++ caller)) := by
  obtain ⟨f,hf,hpair,hmatches⟩ := matchAtoms_freshenRuleAvoiding_closed_origin
    counter (Metta.Minimal.queryOpAvoid prev target caller) rule.1 rule.2 target htarget
  refine ⟨f,hf,hpair,?_⟩
  have hframe := queryOpItemsOfRule_closed_frame prev target caller counter rule htarget hcaller
  change Metta.Minimal.queryOpItemsOfRule prev target caller counter rule = _ at hframe
  rw [hframe,hmatches,List.map_map]
  apply List.map_congr_left
  intro source hs
  rw [hpair]
  dsimp only [Function.comp_def]
  rw [instantiate_renBy_of_renamed_closed_bindings f hf source rule.2
    (matchAtoms_closed_value_mem rule.1 target source htarget hs)]

/-- A unique source match with a closed readout yields exactly that runtime
value, independent of caller bindings and of the chosen collision-free names. -/
theorem queryOpItemsOfRule_closed_single_source
    (prev : Stack) (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom) (source : Metta.Bindings) (value : Metta.Atom)
    (htarget : target.vars = []) (hcaller : Metta.Bindings.hasLoop caller = false)
    (hmatch : Metta.matchAtoms rule.1 target = [source])
    (hreadout : Metta.instantiate source rule.2 = value) (hvalue : value.vars = []) :
    ∃ f : VarName → VarName, Function.Injective f ∧
      Metta.Minimal.queryOpItemsOfRule prev target caller counter rule =
        [evalResult prev value ((renameBindings f source).reverse ++ caller)] := by
  obtain ⟨f,hf,_hpair,hitems⟩ :=
    queryOpItemsOfRule_closed_source_map prev target caller counter rule htarget hcaller
  refine ⟨f,hf,?_⟩
  simpa only [hmatch,List.map_cons,List.map_nil,hreadout,
    renBy_eq_self_of_vars_nil f value hvalue] using hitems

/-- Reading a closed non-function rule value erases only private variable
spellings. Actual candidate occurrences and their retained callers stay intact. -/
theorem queryOpItemsOfRule_closed_values
    (target : Metta.Atom) (caller : Metta.Bindings) (counter : Nat)
    (rule : Metta.Atom × Metta.Atom)
    (ht : target.vars = []) (hc : Metta.Bindings.hasLoop caller = false)
    (hValues : ∀ source ∈ Metta.matchAtoms rule.1 target,
      (Metta.instantiate source rule.2).vars = [] ∧
      isFunctionResult (Metta.instantiate source rule.2) = false) :
    (Metta.Minimal.queryOpItemsOfRule [] target caller counter rule).map
        (fun item => (finalPair item).1) =
      (Metta.matchAtoms rule.1 target).map (fun source => Metta.instantiate source rule.2) ∧
    ∀ item ∈ Metta.Minimal.queryOpItemsOfRule [] target caller counter rule,
      isFinal item = true := by
  obtain ⟨f,_hf,_hpair,hitems⟩ :=
    queryOpItemsOfRule_closed_source_map [] target caller counter rule ht hc
  rw [hitems]
  constructor
  · rw [List.map_map]
    apply List.map_congr_left
    intro source hs
    rcases hValues source hs with ⟨hclosed,hfun⟩
    dsimp only [Function.comp_def]
    rw [renBy_eq_self_of_vars_nil f _ hclosed,
      evalResult_nil_eq_finItem_of_not_function hfun]
    change Metta.instantiate _ (Metta.instantiate source rule.2) = _
    exact instantiate_eq_self_of_vars_nil _ hclosed
  · intro item hi
    rcases List.mem_map.mp hi with ⟨source,hs,rfl⟩
    rcases hValues source hs with ⟨hclosed,hfun⟩
    rw [renBy_eq_self_of_vars_nil f _ hclosed,
      evalResult_nil_eq_finItem_of_not_function hfun]
    rfl

/-- The candidate scan preserves the whole list of closed source values. No
assumption about the caller's representation or a preferred freshening branch
is needed. -/
theorem queryOpFold_closed_values
    (target : Metta.Atom) (caller : Metta.Bindings)
    (ht : target.vars = []) (hc : Metta.Bindings.hasLoop caller = false)
    (rules : List (Metta.Atom × Metta.Atom))
    (hValues : ∀ rule ∈ rules, ∀ source ∈ Metta.matchAtoms rule.1 target,
      (Metta.instantiate source rule.2).vars = [] ∧
      isFunctionResult (Metta.instantiate source rule.2) = false)
    (acc : List Item) (st : St) :
    ((rules.foldl (Metta.Minimal.queryOpFoldStep [] target caller) (acc,st)).1).map
      (fun item => (finalPair item).1) =
      acc.map (fun item => (finalPair item).1) ++
        rules.flatMap (fun rule => (Metta.matchAtoms rule.1 target).map
          (fun source => Metta.instantiate source rule.2)) ∧
    ((∀ item ∈ acc, isFinal item = true) →
      ∀ item ∈ (rules.foldl (Metta.Minimal.queryOpFoldStep [] target caller) (acc,st)).1,
        isFinal item = true) := by
  induction rules generalizing acc st with
  | nil => simp
  | cons rule rules ih =>
    have hRule := queryOpItemsOfRule_closed_values target caller st.counter rule ht hc
      (hValues rule (by simp))
    have hTail := ih (fun other ho => hValues other (by simp [ho]))
      (acc ++ Metta.Minimal.queryOpItemsOfRule [] target caller st.counter rule)
      {st with counter := st.counter + 1}
    simp only [List.foldl_cons,Metta.Minimal.queryOpFoldStep,freshenRuleAvoiding_counter]
    constructor
    · rw [hTail.1,List.map_append,hRule.1,List.flatMap_cons,List.append_assoc]
    · intro hAcc item hItem
      apply hTail.2 ?_ item hItem
      intro member hm
      rcases List.mem_append.mp hm with hold | hnew
      · exact hAcc member hold
      · exact hRule.2 member hnew

/-- A computed singleton source frontier determines one actual root result.
The accompanying theory is retained existentially, rather than replaced by an
empty or normalized caller. -/
theorem queryOp_closed_unique_value
    (env : MinEnv) (st : St) (target value : Metta.Atom) (caller : Metta.Bindings)
    (ht : target.vars = []) (hc : Metta.Bindings.hasLoop caller = false)
    (hHead : isVariableHeaded target = false)
    (hSource : (candidatesW env st.world target).flatMap
      (fun rule => (Metta.matchAtoms rule.1 target).map
        (fun source => Metta.instantiate source rule.2)) = [value])
    (hClosed : value.vars = []) (hFun : isFunctionResult value = false) :
    ∃ bindings,
      (queryOp env st [] target caller).1.map finalPair = [(value,bindings)] ∧
      (∀ item ∈ (queryOp env st [] target caller).1, isFinal item = true) ∧
      (queryOp env st [] target caller).2 =
        {counter := st.counter + (candidatesW env st.world target).length, world := st.world} := by
  have hValues : ∀ rule ∈ candidatesW env st.world target,
      ∀ source ∈ Metta.matchAtoms rule.1 target,
        (Metta.instantiate source rule.2).vars = [] ∧
        isFunctionResult (Metta.instantiate source rule.2) = false := by
    intro rule hr source hs
    have hmem : Metta.instantiate source rule.2 ∈
        (candidatesW env st.world target).flatMap
          (fun rule => (Metta.matchAtoms rule.1 target).map
            (fun source => Metta.instantiate source rule.2)) :=
      List.mem_flatMap.mpr ⟨rule,hr,List.mem_map.mpr ⟨source,hs,rfl⟩⟩
    rw [hSource] at hmem
    have heq := List.mem_singleton.mp hmem
    simpa only [heq] using And.intro hClosed hFun
  let result := (candidatesW env st.world target).foldl
    (Metta.Minimal.queryOpFoldStep [] target caller) ([],st)
  have hFold := queryOpFold_closed_values target caller ht hc
    (candidatesW env st.world target) hValues [] st
  have hMap : result.1.map (fun item => (finalPair item).1) = [value] := by
    simpa only [List.map_nil,List.nil_append,hSource] using hFold.1
  have hFinal : ∀ item ∈ result.1, isFinal item = true :=
    hFold.2 (by simp)
  have hItems : ∃ item, result.1 = [item] ∧ (finalPair item).1 = value := by
    cases h : result.1 with
    | nil => simp [h] at hMap
    | cons item items =>
      rw [h,List.map_cons] at hMap
      have hParts := List.cons.inj hMap
      have hNil : items = [] := List.map_eq_nil_iff.mp hParts.2
      exact ⟨item,by simp [hNil],hParts.1⟩
  obtain ⟨item,hItems,hValue⟩ := hItems
  have hState : result.2 =
      {counter := st.counter + (candidatesW env st.world target).length,world := st.world} := by
    have hcounter := queryOpFold_counter [] target caller
      (candidatesW env st.world target) [] st
    have hworld := queryOpFold_world [] target caller
      (candidatesW env st.world target) [] st
    change result.2.counter = _ at hcounter
    change result.2.world = _ at hworld
    cases hs : result.2 with
    | mk counter world =>
      simp only [hs] at hcounter hworld
      simp only [hcounter,hworld]
  have hQuery : queryOp env st [] target caller = result := by
    unfold queryOp
    rw [hHead]
    change (if result.1.isEmpty = true then _ else result) = result
    simp [hItems]
  refine ⟨(finalPair item).2,?_,?_,?_⟩
  · rw [hQuery,hItems]
    simp only [List.map_cons,List.map_nil]
    congr 1
    exact Prod.ext hValue rfl
  · simpa only [hQuery] using hFinal
  · simpa only [hQuery] using hState

/-- If the original rules have no match, scoped freshening cannot introduce
one. This refusal law requires no well-formedness premise on the caller. -/
theorem queryOp_closed_no_source
    (env : MinEnv) (st : St) (target : Metta.Atom) (caller : Metta.Bindings)
    (ht : target.vars = []) (hHead : isVariableHeaded target = false)
    (hSource : ∀ rule ∈ candidatesW env st.world target,
      Metta.matchAtoms rule.1 target = []) :
    queryOp env st [] target caller =
      ([finItem [] notReducibleA caller],
        {counter := st.counter + (candidatesW env st.world target).length,world := st.world}) := by
  let result := (candidatesW env st.world target).foldl
    (Metta.Minimal.queryOpFoldStep [] target caller) ([],st)
  have hItems : result.1 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro item hi
    rcases queryOpFold_mem_origin [] target caller _ [] st item hi with hn | hr
    · cases hn
    · obtain ⟨rule,hr,counter,hitem⟩ := hr
      obtain ⟨_f,_hf,_hp,horigin⟩ :=
        queryOpItemsOfRule_closed_source_origins [] target caller counter rule ht
      obtain ⟨source,hs,_⟩ := (horigin item).mp hitem
      rw [hSource rule hr] at hs
      cases hs
  have hCounter := queryOpFold_counter [] target caller
    (candidatesW env st.world target) [] st
  have hWorld := queryOpFold_world [] target caller
    (candidatesW env st.world target) [] st
  change result.2.counter = _ at hCounter
  change result.2.world = _ at hWorld
  have hState : result.2 =
      {counter := st.counter + (candidatesW env st.world target).length,world := st.world} := by
    cases hs : result.2 with
    | mk counter world =>
      simp only [hs] at hCounter hWorld
      simp only [hCounter,hWorld]
  unfold queryOp
  rw [hHead]
  change (if result.1.isEmpty = true then
    ([finItem [] notReducibleA caller],result.2) else result) = _
  simp [hItems,hState]

end ClosedSourceObservations

/-! ## Fresh names through evaluator resolution and projection -/

theorem resolveAtom_preserves_outside
    {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) (fuel : Nat) (atom : Metta.Atom)
    (atomAvoids : fresh ∉ atom.vars) :
    fresh ∉ (Metta.Minimal.resolveAtom bindings fuel atom).vars := by
  induction fuel generalizing atom with
  | zero => exact atomAvoids
  | succ fuel ih =>
      unfold Metta.Minimal.resolveAtom
      dsimp only
      split
      · exact atomAvoids
      · exact ih _ (instantiate_preserves_outside outside atom atomAvoids)

theorem resolveAtom_var_outside
    {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) (fuel : Nat) :
    Metta.Minimal.resolveAtom bindings fuel (.var fresh) = .var fresh := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      have reflexive : (Metta.Atom.var fresh == .var fresh) = true := by
        change (fresh == fresh) = true
        simp
      simp only [Metta.Minimal.resolveAtom, instantiate_var_outside outside,
        reflexive, ↓reduceIte]

/-- Projection cannot invent a variable, including a requested but unbound
name. Whole binding support includes names occurring inside stored values. -/
theorem restrictBndRaw_preserves_outside
    (scope : List String) {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) :
    fresh ∉ (Metta.Minimal.restrictBndRaw scope bindings).vars := by
  intro member
  rw [Metta.Minimal.restrictBndRaw, bindings_vars_append_iff] at member
  rcases member with solved | equalities
  · simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap] at solved
    obtain ⟨relation, present, mentioned⟩ := solved
    obtain ⟨key, _, projected⟩ := List.mem_filterMap.mp present
    by_cases keyDifferent : key = fresh
    · subst key
      simp [resolveAtom_var_outside outside] at projected
    ·
      have resolvedAvoids := resolveAtom_preserves_outside outside (bindings.length + 1)
        (.var key) (by simpa [Metta.Atom.vars, eq_comm] using keyDifferent)
      cases value : Metta.Minimal.resolveAtom bindings (bindings.length + 1) (.var key) with
      | sym symbol | gnd ground | expr children =>
          simp only [value, Option.some.injEq] at projected
          subst relation
          simp only [List.mem_cons] at mentioned
          rcases mentioned with equal | inValue
          · exact keyDifferent equal.symm
          · exact resolvedAvoids (by simpa only [value] using inValue)
      | var other =>
          simp only [value] at projected
          split at projected
          · cases projected
          · simp only [Option.some.injEq] at projected
            subst relation
            simp only [List.mem_cons, List.not_mem_nil, or_false] at mentioned
            rcases mentioned with equal | equal
            · exact keyDifferent equal.symm
            · exact resolvedAvoids (by simp [value, Metta.Atom.vars, equal])
  · simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap] at equalities
    obtain ⟨relation, present, mentioned⟩ := equalities
    exact outside (bindingRelation_vars_subset (List.mem_of_mem_filter present)
      (by simpa [Metta.Bindings.vars] using mentioned))

theorem restrictBnd_preserves_outside
    (scope : List String) {bindings : Metta.Bindings} {fresh : String}
    (outside : fresh ∉ bindings.vars) :
    fresh ∉ (Metta.Minimal.restrictBnd scope bindings).vars := by
  have rawAvoids := restrictBndRaw_preserves_outside scope outside
  unfold Metta.Minimal.restrictBnd
  dsimp only
  cases head : (Metta.Bindings.merge [] (Metta.Minimal.restrictBndRaw scope bindings)).head? with
  | none => simpa only [head, Option.getD_none] using rawAvoids
  | some result =>
      simpa only [head, Option.getD_some] using
        merge_preserves_outside (List.mem_of_head? head) (by simp [Metta.Bindings.vars]) rawAvoids

theorem restrictBnd_eq_nil_of_all_outside
    (scope : List VarName) (caller : Metta.Bindings)
    (outside : ∀ name ∈ scope, name ∉ caller.vars) :
    Metta.Minimal.restrictBnd scope caller = [] := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness.restrictBnd_eq_nil_of_resolves_self_and_no_public_eqs
  · intro name member
    exact resolveAtom_var_outside (outside name member) _
  · apply List.filter_eq_nil_iff.mpr
    intro relation member
    cases relation with
    | val key value => simp
    | eq left right =>
        have absent : left ∉ scope := by
          intro present
          exact outside left present (bindingRelation_vars_subset member
            (by simp [Metta.Bindings.vars]))
        simp [absent]

/-! ## Retained public projections -/

/-- A fixed instantiation stays fixed for every remaining iteration budget;
this does not require reflexive host floating-point equality. -/
theorem minimalResolveAtom_eq_of_instantiate_fixed
    (bindings : Metta.Bindings) (atom : Metta.Atom)
    (fixed : Metta.instantiate bindings atom=atom) (fuel : Nat) :
    Metta.Minimal.resolveAtom bindings fuel atom=atom := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [Metta.Minimal.resolveAtom,fixed]
    split
    · rfl
    · exact ih

/-- Every positive projection budget computes exactly the canonical native
readout of a variable in an accepted binding record. -/
theorem minimalResolveAtom_var_eq_instantiate_of_hasLoop_false
    {bindings : Metta.Bindings} (admitted : Metta.Bindings.hasLoop bindings=false)
    (key : String) (fuel : Nat) :
    Metta.Minimal.resolveAtom bindings (fuel+1) (.var key)=Metta.instantiate bindings (.var key) := by
  rw [Metta.Minimal.resolveAtom]
  split
  · rename_i same
    change Metta.Atom.beq (Metta.instantiate bindings (.var key)) (.var key)=true at same
    cases value : Metta.instantiate bindings (.var key) with
    | sym symbol | gnd ground | expr children => simp [value,Metta.Atom.beq] at same
    | var other =>
      have equal : other=key := by simpa [value,Metta.Atom.beq] using same
      simp [equal]
  · exact minimalResolveAtom_eq_of_instantiate_fixed _ _
      (instantiate_idempotent_of_hasLoop_false admitted (.var key)) fuel

/-- Accepted native records with the same public readouts and public equality
rows have the same retained projection, including its canonical merge. -/
theorem restrictBnd_eq_of_admitted_readouts
    (scope : List String) (left right : Metta.Bindings)
    (leftAdmitted : Metta.Bindings.hasLoop left=false)
    (rightAdmitted : Metta.Bindings.hasLoop right=false)
    (readouts : ∀ key ∈ scope,
      Metta.instantiate left (.var key)=Metta.instantiate right (.var key))
    (publicEqualities : left.filter (fun relation => match relation with
        | .eq first second => scope.contains first && scope.contains second
        | _ => false) = right.filter (fun relation => match relation with
        | .eq first second => scope.contains first && scope.contains second
        | _ => false)) :
    Metta.Minimal.restrictBnd scope left=Metta.Minimal.restrictBnd scope right := by
  have raw : Metta.Minimal.restrictBndRaw scope left=Metta.Minimal.restrictBndRaw scope right := by
    unfold Metta.Minimal.restrictBndRaw
    dsimp only
    apply congrArg₂ List.append
    · apply List.filterMap_congr
      intro key present
      rw [minimalResolveAtom_var_eq_instantiate_of_hasLoop_false leftAdmitted,
        minimalResolveAtom_var_eq_instantiate_of_hasLoop_false rightAdmitted,
        readouts key present]
    · exact publicEqualities
  unfold Metta.Minimal.restrictBnd
  rw [raw]

/-- Projection discards an isolated local component when its public holes are
literal and no local equality has both endpoints in the public scope. The
scope may include arbitrarily many public holes and all caller variables. -/
theorem restrictBnd_append_disjoint_frame
    (scope : List String) {front frame : Metta.Bindings}
    (disjoint : List.Disjoint front.vars frame.vars)
    (frontAdmitted : Metta.Bindings.hasLoop front=false)
    (frameAdmitted : Metta.Bindings.hasLoop frame=false)
    (publicLiteral : ∀ key ∈ scope,key ∈ front.vars →
      Metta.instantiate front (.var key)=.var key)
    (hiddenEdges : ∀ first second,.eq first second ∈ front →
      (scope.contains first && scope.contains second)=false) :
    Metta.Minimal.restrictBnd scope (front++frame)=Metta.Minimal.restrictBnd scope frame := by
  apply restrictBnd_eq_of_admitted_readouts scope (front++frame) frame
    (hasLoop_false_append_disjoint disjoint frontAdmitted frameAdmitted) frameAdmitted
  · intro key present
    by_cases inFront : key ∈ front.vars
    · have outside : key ∉ frame.vars := List.disjoint_left.mp disjoint inFront
      rw [instantiate_append_disjoint_frame disjoint (.var key)
          (by simpa [Metta.Atom.vars] using outside),
        publicLiteral key present inFront,instantiate_var_outside outside]
    · exact instantiate_append_disjoint_left_frame disjoint (.var key)
        (by simpa [Metta.Atom.vars] using inFront)
  · rw [List.filter_append]
    have localEmpty : front.filter (fun relation => match relation with
        | .eq first second => scope.contains first && scope.contains second
        | _ => false)=[] := by
      apply List.filter_eq_nil_iff.mpr
      intro relation present
      cases relation with
      | val key value => simp
      | eq first second => exact Bool.eq_false_iff.mp (hiddenEdges first second present)
    rw [localEmpty,List.nil_append]

/-! ## Fresh local application admission -/

section FreshLocalApplication

open Metta Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness

/-- Public holes distinct from the private local-rule keys stay open under
the equality-first rule record. This includes several future local binders. -/
theorem instantiate_local_let_public_holes
    (pattern atomKey templateKey binder : VarName) (payload template atom : Atom)
    (patternBinder : pattern ≠ binder)
    (atomPattern : atomKey ≠ pattern) (templatePattern : templateKey ≠ pattern)
    (atomBinder : atomKey ≠ binder) (templateBinder : templateKey ≠ binder)
    (holes : ∀ key ∈ atom.vars, key ≠ pattern ∧ key ≠ atomKey ∧ key ≠ templateKey) :
    Metta.instantiate [.eq pattern binder, .val atomKey payload, .val templateKey template] atom = atom := by
  apply instantiate_eq_self_of_valueless_representatives
  · intro key mentioned
    obtain ⟨notPattern, notAtom, notTemplate⟩ := holes key mentioned
    exact Bindings.classValues_one_eq_two_vals_eq_nil pattern binder atomKey templateKey
      key payload template patternBinder notPattern notAtom notTemplate
        atomPattern.symm templatePattern.symm atomBinder.symm templateBinder.symm
  · intro key mentioned
    exact Bindings.eqRepresentative_one_eq_two_vals_of_ne_left pattern binder atomKey
      templateKey key payload template patternBinder (holes key mentioned).1

/-- The equality-first runtime rule record passes native loop admission and
materializes its operand and template, keeping public holes available. -/
theorem local_let_record_readout
    (pattern atomKey templateKey binder : VarName) (payload template : Atom)
    (patternBinder : pattern ≠ binder)
    (atomPattern : atomKey ≠ pattern) (templatePattern : templateKey ≠ pattern)
    (atomBinder : atomKey ≠ binder) (templateBinder : templateKey ≠ binder)
    (atomTemplate : atomKey ≠ templateKey)
    (closed : payload.vars = [])
    (holes : ∀ key ∈ template.vars, key ≠ pattern ∧ key ≠ atomKey ∧ key ≠ templateKey)
    (templateNonvar : ∀ key, template ≠ .var key) :
    Metta.Bindings.hasLoop [.eq pattern binder, .val atomKey payload, .val templateKey template] = false ∧
    Metta.instantiate [.eq pattern binder, .val atomKey payload, .val templateKey template]
      (.expr [.sym "unify", .var atomKey, .var pattern, .var templateKey, .sym "Empty"]) =
      .expr [.sym "unify", payload, .var binder, template, .sym "Empty"] := by
  let record : Metta.Bindings := [.eq pattern binder, .val atomKey payload, .val templateKey template]
  have patternClass : Metta.Bindings.eqClassOrdered record pattern = [binder,pattern] :=
    Bindings.eqClassOrdered_one_eq_two_vals_left pattern binder atomKey templateKey
      payload template patternBinder
  have atomClass : Metta.Bindings.eqClassOrdered record atomKey = [atomKey] := by
    simpa only [if_neg atomBinder] using
      Bindings.eqClassOrdered_one_eq_two_vals_of_ne_left pattern binder atomKey templateKey
        atomKey payload template patternBinder atomPattern
  have templateClass : Metta.Bindings.eqClassOrdered record templateKey = [templateKey] := by
    simpa only [if_neg templateBinder] using
      Bindings.eqClassOrdered_one_eq_two_vals_of_ne_left pattern binder atomKey templateKey
        templateKey payload template patternBinder templatePattern
  have atomValues : Metta.Bindings.classValues record atomKey = [payload] :=
    Bindings.classValues_one_eq_two_vals_key1 pattern binder atomKey templateKey
      payload template patternBinder atomPattern atomBinder atomTemplate
  have templateValues : Metta.Bindings.classValues record templateKey = [template] :=
    Bindings.classValues_one_eq_two_vals_key2 pattern binder atomKey templateKey
      payload template patternBinder templatePattern templateBinder atomTemplate.symm
  have patternValues : Metta.Bindings.classValues record pattern = [] :=
    Bindings.classValues_one_eq_two_vals_left_eq_nil pattern binder atomKey templateKey
      payload template patternBinder atomPattern.symm templatePattern.symm
        atomBinder.symm templateBinder.symm
  have atomSize : payload.size < (Metta.Bindings.resolutionFuel record (.var atomKey)).pred := by
    simp [record, Metta.Bindings.resolutionFuel, Metta.Bindings.relationResolutionFuel, Atom.size]
    omega
  have templateSize : template.size < (Metta.Bindings.resolutionFuel record (.var templateKey)).pred := by
    simp [record, Metta.Bindings.resolutionFuel, Metta.Bindings.relationResolutionFuel, Atom.size]
    omega
  have atomResolved : Metta.Bindings.resolve record atomKey = some payload :=
    Bindings.resolve_eq_closed_class_value atomClass atomValues closed atomSize
  have patternResolved : Metta.Bindings.resolve record pattern = some (.var binder) := by
    apply Bindings.resolve_eq_representative_of_valueless_class patternClass
    · simp
    · exact patternValues
    · simp [Metta.Bindings.eqRepresentative, patternClass]
  have templateAux : Metta.Bindings.resolveAtomAux record
      (Metta.Bindings.resolutionFuel record (.var templateKey)).pred [templateKey] template =
        some template := by
    apply Bindings.resolveAtomAux_inert
    · intro key mentioned
      obtain ⟨notPattern, notAtom, notTemplate⟩ := holes key mentioned
      exact Bindings.classValues_one_eq_two_vals_eq_nil pattern binder atomKey templateKey
        key payload template patternBinder notPattern notAtom notTemplate
          atomPattern.symm templatePattern.symm atomBinder.symm templateBinder.symm
    · intro key mentioned
      exact Bindings.eqRepresentative_one_eq_two_vals_of_ne_left pattern binder atomKey
        templateKey key payload template patternBinder (holes key mentioned).1
    · intro key mentioned other member
      have observed := Bindings.eqClassOrdered_one_eq_two_vals_of_ne_left pattern binder atomKey
        templateKey key payload template patternBinder (holes key mentioned).1
      change other ∈ Metta.Bindings.eqClassOrdered
        [.eq pattern binder, .val atomKey payload, .val templateKey template] key at member
      rw [observed] at member
      by_cases same : key = binder
      · rw [if_pos same] at member
        have cases : other = binder ∨ other = pattern := by simpa using member
        rcases cases with rfl | rfl
        · simpa using templateBinder.symm
        · simpa using templatePattern.symm
      · rw [if_neg same] at member
        have equal : other = key := by simpa using member
        subst other
        simpa using (holes key mentioned).2.2
    · exact templateSize
  have templateResolved : Metta.Bindings.resolve record templateKey = some template :=
    Bindings.resolve_eq_nonvar_class_value templateClass templateValues templateNonvar templateAux
  have admitted : record.hasLoop = false := by
    apply Bindings.hasLoop_false_of_resolveAtomAux_some
    · have payloadNonvar : ∀ key, payload ≠ .var key := by
        intro key same
        subst payload
        simp [Atom.vars] at closed
      cases payload with
      | var name => exact False.elim (payloadNonvar name rfl)
      | sym symbol | gnd ground | expr children =>
        cases template with
        | var name => exact False.elim (templateNonvar name rfl)
        | sym symbol | gnd ground | expr children =>
          simp [record, patternBinder]
    · intro key _
      by_cases samePattern : key = pattern
      · subst key
        exact Bindings.resolveAtomAux_some_of_resolve_some patternResolved
      by_cases sameAtom : key = atomKey
      · subst key
        exact Bindings.resolveAtomAux_some_of_resolve_some atomResolved
      by_cases sameTemplate : key = templateKey
      · subst key
        exact Bindings.resolveAtomAux_some_of_resolve_some templateResolved
      refine ⟨.var key, ?_⟩
      apply Bindings.resolveAtomAux_inert
      · intro other mentioned
        have same : other = key := by simpa only [Atom.vars, List.mem_singleton] using mentioned
        subst other
        exact Bindings.classValues_one_eq_two_vals_eq_nil pattern binder atomKey templateKey
          key payload template patternBinder samePattern sameAtom sameTemplate
            atomPattern.symm templatePattern.symm atomBinder.symm templateBinder.symm
      · intro other mentioned
        have same : other = key := by simpa only [Atom.vars, List.mem_singleton] using mentioned
        subst other
        exact Bindings.eqRepresentative_one_eq_two_vals_of_ne_left pattern binder atomKey
          templateKey key payload template patternBinder samePattern
      · intros
        simp
      · simp [Metta.Bindings.resolutionFuel, Atom.size]
  refine ⟨admitted, ?_⟩
  change Metta.instantiate record _ = _
  simp [Metta.instantiate, Metta.Bindings.resolveAtom, atomResolved, patternResolved, templateResolved]

#guard Metta.instantiate
    [.eq "private-pattern" "x", .val "private-atom" (.sym "value"),
      .val "private-template" (.expr [.sym "pair", .var "x", .var "y", .var "x"])]
    (.expr [.sym "unify", .var "private-atom", .var "private-pattern",
      .var "private-template", .sym "Empty"]) ==
    .expr [.sym "unify", .sym "value", .var "x",
      .expr [.sym "pair", .var "x", .var "y", .var "x"], .sym "Empty"]

#guard Metta.instantiate
    [.eq "private-pattern" "x", .val "private-atom" (.sym "value"),
      .val "private-template" (.expr [.sym "pair", .var "private-atom"])]
    (.var "private-template") != .expr [.sym "pair", .var "private-atom"]

theorem instantiate_fresh_local_application
    (caller : Metta.Bindings) (op key : VarName) (payload template : Metta.Atom)
    (fresh : key ∉ caller.vars) (closed : payload.vars = [])
    (covered : ∀ name ∈ template.vars, name = key) :
    Metta.instantiate caller (.expr [.sym op, .var key, payload, template]) =
      .expr [.sym op, .var key, payload, template] := by
  apply instantiate_eq_self_of_outside_vars
  intro name member
  have cases : name = key ∨ name ∈ template.vars := by
    simpa [Metta.Atom.vars, closed] using member
  rcases cases with rfl | inTemplate
  · exact fresh
  · rw [covered name inTemplate]
    exact fresh

theorem fresh_local_application_visible_scope_outside
    (caller : Metta.Bindings) (op key : VarName) (payload template : Metta.Atom)
    (fresh : key ∉ caller.vars) (closed : payload.vars = [])
    (covered : ∀ name ∈ template.vars, name = key) :
    ∀ name ∈ expectedApplicationVisibleScope
      (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%"),
      name ∉ caller.vars := by
  intro name member
  have cases : name = key ∨ name ∈ template.vars := by
    simpa [expectedApplicationVisibleScope, Metta.Atom.vars, closed] using member
  rcases cases with rfl | inTemplate
  · exact fresh
  · rw [covered name inTemplate]
    exact fresh

theorem fresh_local_application_initial_bindings
    (caller : Metta.Bindings) (op key : VarName) (payload template : Metta.Atom)
    (fresh : key ∉ caller.vars) (closed : payload.vars = [])
    (covered : ∀ name ∈ template.vars, name = key) :
    selectedApplicationInitialBindingsFromTheory caller
      (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%") caller = [caller] := by
  apply selectedApplicationInitialBindingsFromTheory_of_empty_projection
  apply restrictBnd_eq_nil_of_all_outside
  exact fresh_local_application_visible_scope_outside caller op key payload template
    fresh closed covered

theorem selected_let_plan_fresh_local_seed
    (env : MinEnv) (world : World) (op key : VarName) (payload template : Metta.Atom)
    (caller : Metta.Bindings) (fresh : key ∉ caller.vars) (closed : payload.vars = [])
    (covered : ∀ name ∈ template.vars, name = key)
    (admitted : caller.hasLoop = false)
    (signature : getTypes env (typePrep world (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom", .sym "%Undefined%"]]) :
    (selectedApplicationExecutionPlan_let_policy_from env world op (.var key) payload template
      caller admitted signature).seeds = [caller] := by
  simpa only [SelectedApplicationExecutionPlan.seeds,
    selectedApplicationExecutionPlan_let_policy_from] using
    fresh_local_application_initial_bindings caller op key payload template fresh closed covered

/-- A rejected caller at the known lazy local-binding signature is refused
before its middle argument or either continuation can run. -/
theorem mettaEval_fresh_let_cyclic_refusal
    (env : MinEnv) (fuel : Nat) (st : St) (op key : VarName) (payload template : Metta.Atom)
    (caller : Metta.Bindings) (fresh : key ∉ caller.vars) (closed : payload.vars = [])
    (covered : ∀ name ∈ template.vars, name = key)
    (notError : (Atom.expr [.sym op, .var key, payload, template]).isError = false)
    (cyclic : caller.hasLoop = true)
    (signature : getTypes env (typePrep st.world (.sym op)) =
      [.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom", .sym "%Undefined%"]]) :
    mettaEval env (fuel + 1) st caller (.expr [.sym op, .var key, payload, template]) =
      ([(badTypeAtom (.sym op)
        (.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom", .sym "%Undefined%"])
        (.expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom", .sym "%Undefined%"]),caller)],st) := by
  let selected : SelectedFunctionType :=
    { functionType := .expr [.sym "->", .sym "Atom", .sym "%Undefined%", .sym "Atom", .sym "%Undefined%"]
      argumentTypes := [.sym "Atom", .sym "%Undefined%", .sym "Atom"]
      returnType := .sym "%Undefined%"
      typeBindings := caller }
  have scan := Metta.selectFunctionTypeForExpectedFrom_let_policy_selected_from
    env st.world op (.var key) payload template caller signature
  have head := mettaTypeCastAvoiding_symbolic_arrow_from_eq
    (expectedApplicationVisibleScope (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%"))
    env st.world caller op ["Atom", "%Undefined%", "Atom", "%Undefined%"] signature
  rw [cyclic] at head
  have headSelected : mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%"))
      env st.world caller (.sym op) selected.functionType =
        .inl [selected.functionType] := by
    simpa only [selected, List.map_cons, List.map_nil, ↓reduceIte] using head
  have seeds := fresh_local_application_initial_bindings caller op key payload template fresh closed covered
  have unchanged := instantiate_fresh_local_application caller op key payload template fresh closed covered
  conv_lhs => unfold mettaEval
  rw [unchanged]
  have notEmpty : (Atom.expr [.sym op, .var key, payload, template] == emptyA) = false := rfl
  simp only [notEmpty, notError, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  rw [executeApplicationPlan, scan]
  change prioritizeSemanticResults (executeSelectedApplicationPlan _ _ env caller st op
    [.var key, payload, template] (.sym "%Undefined%") selected) = _
  unfold executeSelectedApplicationPlan
  dsimp only
  change prioritizeSemanticResults
    (match mettaTypeCastAvoiding
      (expectedApplicationVisibleScope (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%"))
      env st.world caller (.sym op) selected.functionType with
    | .inl rejected =>
        ((selectedApplicationInitialBindings caller
          (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%") selected).flatMap
          (fun bindings => rejected.map (fun actual => (badTypeAtom (.sym op) selected.functionType actual, bindings))), st)
    | .inr _ => _) = _
  rw [headSelected]
  have seedEq : selectedApplicationInitialBindings caller
      (.expr [.sym op, .var key, payload, template]) (.sym "%Undefined%") selected = [caller] := seeds
  rw [seedEq]
  simp [prioritizeSemanticResults, selected, badTypeAtom, Metta.Atom.isError]

end FreshLocalApplication

namespace DisjointFrameControls

private def localOpen : Metta.Bindings :=
  [.eq "pattern" "local", .val "local" (.expr [.sym "f", .var "open"])]
private def cyclicCaller : Metta.Bindings :=
  [.val "left" (.var "right"), .val "right" (.var "left")]
private def localQuery : Metta.Atom := .expr [.var "pattern", .var "open"]
private def localValue : Metta.Atom := .expr [.expr [.sym "f", .var "open"], .var "open"]

-- An open local component keeps its aliases and unresolved variables even
-- beside a cyclic caller. These are observations of actual native functions.
#guard Metta.Bindings.hasLoop cyclicCaller
#guard Metta.instantiate localOpen localQuery == localValue
#guard Metta.instantiate (localOpen ++ cyclicCaller) localQuery == localValue
#guard Metta.Bindings.eqClassOrdered (localOpen ++ cyclicCaller) "pattern" ==
  Metta.Bindings.eqClassOrdered localOpen "pattern"
#guard Metta.Bindings.classValues (localOpen ++ cyclicCaller) "pattern" ==
  Metta.Bindings.classValues localOpen "pattern"
#guard Metta.Bindings.resolveAtomAux (localOpen ++ cyclicCaller) 1 [] localQuery ==
  Metta.Bindings.resolveAtomAux localOpen 1 [] localQuery

private def localCycle : Metta.Bindings :=
  [.val "local" (.expr [.sym "f", .var "local"])]
#guard (Metta.Bindings.resolve (localCycle ++ cyclicCaller) "local").isNone
#guard Metta.instantiate (localCycle ++ cyclicCaller) (.var "local") == (.var "local")

-- Disjoint value keys alone are insufficient: a nested free variable in the
-- local value can be captured by an otherwise differently named caller.
private def overlappingCaller : Metta.Bindings := [.val "open" (.sym "captured")]
#guard Metta.instantiate (localOpen ++ overlappingCaller) (.var "pattern") ==
  .expr [.sym "f", .sym "captured"]
#guard !(Metta.instantiate (localOpen ++ overlappingCaller) localQuery == localValue)

-- A foreign equality edge can create the same capture without a direct
-- binding of the locally mentioned variable.
private def aliasOverlap : Metta.Bindings :=
  [.eq "open" "foreign", .val "foreign" (.sym "captured")]
#guard Metta.instantiate (localOpen ++ aliasOverlap) (.var "pattern") ==
  .expr [.sym "f", .sym "captured"]

end DisjointFrameControls

namespace FreshLocalMergeControls
private def caller : Metta.Bindings := [.val "x" (.var "y"), .val "y" (.var "x")]
private def payload : Metta.Atom := .expr [.sym "data"]
private def template : Metta.Atom := .expr [.sym "use", .var "binder"]
private def rows : Metta.Bindings :=
  [.val "private-template" template, .val "private-atom" payload, .eq "private-pattern" "binder"]
private def extended : Metta.Bindings := rows.reverse ++ caller

#guard Metta.Bindings.merge caller rows == [extended]
#guard Metta.Bindings.hasLoop extended
#guard Metta.instantiate extended (.var "private-template") == template
#guard Metta.instantiate extended (.var "private-pattern") == .var "binder"

-- Occupied local keys cause genuine reconciliation or refusal; their old
-- values are not silently overwritten by the fresh-component theorem.
#guard (Metta.Bindings.merge [.val "private-template" (.sym "old")]
  [.val "private-template" (.sym "new")]).isEmpty

-- A variable-valued input produces an equality relation, not a raw value row.
#guard Metta.Bindings.merge caller [.val "private-template" (.var "binder")] ==
  [[.eq "private-template" "binder"] ++ caller]

end FreshLocalMergeControls

namespace DisjointComponentControls
private def localRows : Metta.Bindings :=
  [.eq "pattern" "binder", .val "template" (.expr [.sym "use",.var "binder"])]

-- This raw caller is not a solution of all its stored equations. The native
-- resolver deliberately observes the first class value; framing preserves
-- that exact implementation behavior without assuming class consistency.
private def inconsistentCaller : Metta.Bindings :=
  [.eq "v" "u", .val "u" (.sym "chosen"), .val "v" (.expr [.sym "f", .var "u"])]
#guard !(Metta.Bindings.hasLoop localRows)
#guard !(Metta.Bindings.hasLoop inconsistentCaller)
#guard !(Metta.Bindings.hasLoop (localRows ++ inconsistentCaller))
#guard Metta.instantiate (localRows ++ inconsistentCaller) (.var "v") == .sym "chosen"
#guard !(Metta.instantiate inconsistentCaller (.var "v") ==
  Metta.instantiate inconsistentCaller (.expr [.sym "f",.var "u"]))

private def foreignCycle : Metta.Bindings := [.val "cycle" (.expr [.sym "f", .var "cycle"])]
#guard Metta.Bindings.hasLoop (localRows ++ foreignCycle)
#guard Metta.Bindings.hasLoop (foreignCycle ++ localRows)

-- Without separation, two individually acyclic fragments can form a cycle.
private def firstHalf : Metta.Bindings := [.val "x" (.var "y")]
private def secondHalf : Metta.Bindings := [.val "y" (.var "x")]
#guard !(Metta.Bindings.hasLoop firstHalf)
#guard !(Metta.Bindings.hasLoop secondHalf)
#guard Metta.Bindings.hasLoop (firstHalf ++ secondHalf)

-- Overlapping keys can also hide a selected-value cycle. The disjoint OR law
-- makes no claim at this unadmitted boundary.
#guard !(Metta.Bindings.hasLoop ([.val "cycle" (.sym "chosen")] ++ foreignCycle))

end DisjointComponentControls

namespace DisjointProjectionControls
private def localRows : Metta.Bindings :=
  [.eq "private-pattern" "nx", .val "private-atom" (.expr [.sym "payload"]),
   .val "private-template" (.expr [.sym "pair", .var "nx", .var "ny"])]
private def caller : Metta.Bindings :=
  [.eq "b" "a", .val "a" (.sym "chosen"), .val "b" (.expr [.sym "f", .var "a"])]
private def scope : List String := caller.vars ++ ["nx","ny"]

#guard !(Metta.Bindings.hasLoop localRows)
#guard !(Metta.Bindings.hasLoop caller)
#guard Metta.Minimal.resolveAtom caller 1 (.var "b") == .sym "chosen"
#guard Metta.Minimal.resolveAtom caller 100 (.var "b") == .sym "chosen"
#guard Metta.Minimal.restrictBnd scope (localRows ++ caller) == Metta.Minimal.restrictBnd scope caller
#guard !(Metta.Bindings.vars (Metta.Minimal.restrictBnd scope (localRows ++ caller))).contains "ny"
#guard !(Metta.Bindings.vars (Metta.Minimal.restrictBnd scope (localRows ++ caller))).contains "private-template"

-- Exposing a private equality endpoint or private value key makes that local
-- information public. The projection theorem requires these exclusions.
#guard !(Metta.Minimal.restrictBnd ("private-pattern"::scope) (localRows ++ caller) ==
  Metta.Minimal.restrictBnd ("private-pattern"::scope) caller)
#guard !(Metta.Minimal.restrictBnd ("private-template"::scope) (localRows ++ caller) ==
  Metta.Minimal.restrictBnd ("private-template"::scope) caller)

-- A local assignment to a public hole is an observable result, not discarded
-- merely because the local keys and caller keys are separate.
#guard !(Metta.Minimal.restrictBnd ["nx"] ([.val "nx" (.sym "assigned")] ++ caller) ==
  Metta.Minimal.restrictBnd ["nx"] caller)

end DisjointProjectionControls

namespace BindingSupportControls


-- A valueless aliased local can be filled twice in a template without losing a use.
#guard ((Metta.Minimal.unifyOp [] (.sym "value") (.var "local")
  (.expr [.sym "Pair", .var "local", .var "local"]) (.sym "refused")
  [.eq "pattern" "local", .val "held" (.expr [.sym "P", .var "external"])]).map (fun item => item.stack.map (fun frame => frame.atom))) ==
    [[.expr [.sym "Pair", .sym "value", .sym "value"]]]

-- An occupied class does not pass the valueless-local contract.
#guard ((Metta.Minimal.unifyOp [] (.sym "new") (.var "local")
  (.var "local") (.sym "refused") [.eq "pattern" "local", .val "pattern" (.sym "old")]).map (fun item => item.stack.map (fun frame => frame.atom))) == [[.sym "refused"]]

-- Filling a different class cannot repair a retained caller's cycle.
#guard ((Metta.Minimal.unifyOp [] (.sym "value") (.var "local")
  (.var "local") (.sym "refused") [.eq "pattern" "local", .eq "cycle" "cycle"]).map (fun item => item.stack.map (fun frame => frame.atom))) == [[.sym "refused"]]

/-- Requesting an unbound variable does not insert it into the projected caller. -/
theorem requested_fresh_name_stays_outside :
    "fresh" ∉ (Metta.Minimal.restrictBnd ["x", "fresh"]
      [.val "x" (.var "external")]).vars := by
  apply restrictBnd_preserves_outside
  simp [Metta.Bindings.vars, Metta.Atom.vars]

/-- Open stored values belong to the freshness boundary, not only their keys. -/
theorem name_inside_a_stored_value_is_not_fresh :
    "fresh" ∈ Metta.Bindings.vars
      [.val "x" (.expr [.sym "P", .var "fresh"])] := by
  simp [Metta.Bindings.vars, Metta.Atom.vars]

-- The executable projection retains the requested value's open dependency.
#guard (Metta.Minimal.restrictBnd ["x"]
  [.val "x" (.var "external")]).vars.contains "external"

/-- Reconciliation through an open compound cannot capture an unrelated local. -/
theorem reconciled_open_values_keep_a_fresh_local
    {result : Metta.Bindings}
    (produced : result ∈ Metta.Bindings.merge
      [.val "x" (.expr [.sym "P", .var "external"])]
      [.val "x" (.expr [.sym "P", .sym "value"])]) :
    "fresh" ∉ result.vars := by
  exact merge_preserves_outside produced (by simp [Metta.Bindings.vars, Metta.Atom.vars])
    (by simp [Metta.Bindings.vars, Metta.Atom.vars])

end BindingSupportControls

namespace FreshBinderControls

private def capturedCaller : Metta.Bindings := [.val "body" (.sym "old")]

theorem fresh_local_keeps_the_occupied_caller :
    unifyOp [] (.sym "new") (.var "body#fresh") (.var "body#fresh")
        (.sym "refused") capturedCaller =
      [finItem [] (.sym "new") (.val "body#fresh" (.sym "new") :: capturedCaller)] := by
  rw [unifyOp_closed_fresh_binder_template [] (.sym "new") (.var "body#fresh")
    (.sym "refused") capturedCaller "body#fresh" (by simp [Metta.Atom.vars])
    (by simp [capturedCaller, Metta.Bindings.vars, Metta.Atom.vars])
    (ClosedValueBindings.hasLoop_false
      (ClosedValueBindings.val (by simp [Metta.Atom.vars]) ClosedValueBindings.nil))
    (by simp [Metta.Atom.vars])]
  rw [instantiate_singleton_val_var _ _ (by simp [Metta.Atom.vars])]

theorem occupied_local_is_outside_the_fresh_contract :
    "body" ∈ capturedCaller.vars := by
  simp [capturedCaller, Metta.Bindings.vars, Metta.Atom.vars]

theorem a_fresh_local_cannot_repair_a_cyclic_caller :
    unifyOp [] (.sym "new") (.var "body#fresh") (.var "body#fresh")
        (.sym "refused") [.eq "held" "held"] =
      [finItem [] (.sym "refused") [.eq "held" "held"]] := by
  apply unifyOp_closed_fresh_binder_cyclic
  · simp [Metta.Atom.vars]
  · simp [Metta.Bindings.vars]
  · simp [Metta.Bindings.hasLoop]

theorem distinct_closed_local_values_remain_distinct :
    Metta.instantiate [.val "body#fresh" (.sym "new")] (.var "body#fresh") ≠
      Metta.instantiate capturedCaller (.var "body") := by
  unfold capturedCaller
  rw [instantiate_singleton_val_var _ _ (by simp [Metta.Atom.vars]),
    instantiate_singleton_val_var _ _ (by simp [Metta.Atom.vars])]
  simp

end FreshBinderControls


/-! ## Scoped caller support and public-hole projection -/

section ProjectionReadoutSupport
set_option autoImplicit true
open Metta Metta.Minimal
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Public projection is supported by its requested names and the variables
inside their actual resolved values. Private keys alone do not leak. -/
theorem restrictBndRaw_vars_subset_of_readouts
    (scope support : List String) (bindings : Metta.Bindings)
    (scopeSupport : ∀ key∈scope,key∈support)
    (readSupport : ∀ key∈scope,∀ name∈
      (Minimal.resolveAtom bindings (bindings.length+1) (.var key)).vars,name∈support) :
    ∀ name∈(restrictBndRaw scope bindings).vars,name∈support := by
  intro name member
  rw [restrictBndRaw,bindings_vars_append_iff] at member
  rcases member with solved | equalities
  · simp only [Metta.Bindings.vars,List.mem_eraseDups,List.mem_flatMap] at solved
    obtain ⟨relation,present,mentioned⟩ := solved
    obtain ⟨key,keyPresent,projected⟩ := List.mem_filterMap.mp present
    cases value : Minimal.resolveAtom bindings (bindings.length+1) (.var key) with
    | sym symbol | gnd ground | expr children =>
      simp only [value,Option.some.injEq] at projected
      subst relation
      simp only [List.mem_cons] at mentioned
      rcases mentioned with rfl | inValue
      · exact scopeSupport name keyPresent
      · exact readSupport key keyPresent name (by simpa only [value] using inValue)
    | var other =>
      simp only [value] at projected
      split at projected
      · cases projected
      · simp only [Option.some.injEq] at projected
        subst relation
        simp only [List.mem_cons,List.not_mem_nil,or_false] at mentioned
        rcases mentioned with rfl | rfl
        · exact scopeSupport name keyPresent
        · exact readSupport key keyPresent name (by simp [value,Metta.Atom.vars])
  · simp only [Metta.Bindings.vars,List.mem_eraseDups,List.mem_flatMap] at equalities
    obtain ⟨relation,present,mentioned⟩ := equalities
    have keep := (List.mem_filter.mp present).2
    cases relation with
    | val key value => contradiction
    | eq left right =>
      have both : left∈scope ∧ right∈scope := by simpa using keep
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mentioned
      rcases mentioned with rfl | rfl
      · exact scopeSupport name both.1
      · exact scopeSupport name both.2

/-- Canonical replay of the raw public projection cannot enlarge its support.
This includes the actual fallback when reconciliation has no result. -/
theorem restrictBnd_vars_subset_of_readouts
    (scope support : List String) (bindings : Metta.Bindings)
    (scopeSupport : ∀ key∈scope,key∈support)
    (readSupport : ∀ key∈scope,∀ name∈
      (Minimal.resolveAtom bindings (bindings.length+1) (.var key)).vars,name∈support) :
    ∀ name∈(restrictBnd scope bindings).vars,name∈support := by
  have raw := restrictBndRaw_vars_subset_of_readouts scope support bindings scopeSupport readSupport
  unfold restrictBnd
  dsimp only
  cases head : (Metta.Bindings.merge [] (restrictBndRaw scope bindings)).head? with
  | none => simpa only [head,Option.getD_none] using raw
  | some result =>
    simp only [Option.getD_some]
    intro name member
    rcases merge_vars_subset (List.mem_of_head? head) member with impossible | fromRaw
    · simp [Metta.Bindings.vars] at impossible
    · exact raw name fromRaw

/-- In an accepted record the public support condition can be stated using
the actual native materializer, whose fixed point drives projection. -/
theorem restrictBnd_vars_subset_of_admitted_readouts
    (scope support : List String) (bindings : Metta.Bindings)
    (admitted : bindings.hasLoop=false)
    (scopeSupport : ∀ key∈scope,key∈support)
    (readSupport : ∀ key∈scope,∀ name∈(instantiate bindings (.var key)).vars,name∈support) :
    ∀ name∈(restrictBnd scope bindings).vars,name∈support := by
  apply restrictBnd_vars_subset_of_readouts scope support bindings scopeSupport
  intro key present name member
  rw [minimalResolveAtom_var_eq_instantiate_of_hasLoop_false admitted] at member
  exact readSupport key present name member
end ProjectionReadoutSupport

section BindingReadSupport
set_option autoImplicit true
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A selected region of variable names is closed under the actual stored
value dependencies and both directions of explicit equality. No consistency,
acyclicity, or binding-list layout is assumed. -/
structure BindingReadSupport (support : String → Prop) (bindings : Metta.Bindings) : Prop where
  value : ∀ key atom, Metta.BindingRel.val key atom ∈ bindings →
    support key → ∀ name ∈ atom.vars, support name
  equality : ∀ left right, Metta.BindingRel.eq left right ∈ bindings →
    (support left ↔ support right)

namespace BindingReadSupport
variable {support : String → Prop} {bindings : Metta.Bindings}

theorem of_vars_subset (inside : ∀ name ∈ bindings.vars,support name) :
    BindingReadSupport support bindings := by
  constructor
  · intro key value present _ name mentioned
    exact inside name (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars,mentioned]))
  · intro left right present
    have leftInside := inside left
      (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars]))
    have rightInside := inside right
      (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars]))
    exact ⟨fun _ => rightInside,fun _ => leftInside⟩

/-- A relation may lie wholly inside or wholly outside the selected support.
Interleaving those components does not alter the resolution invariant. -/
theorem of_partition
    (partition : ∀ relation ∈ bindings,
      (∀ name ∈ Metta.Bindings.vars [relation],support name) ∨
      (∀ name ∈ Metta.Bindings.vars [relation],¬support name)) :
    BindingReadSupport support bindings := by
  constructor
  · intro key value present inside name mentioned
    rcases partition (.val key value) present with allInside | allOutside
    · exact allInside name (by simp [Metta.Bindings.vars,mentioned])
    · exact (allOutside key (by simp [Metta.Bindings.vars]) inside).elim
  · intro left right present
    rcases partition (.eq left right) present with allInside | allOutside
    · exact ⟨fun _ => allInside right (by simp [Metta.Bindings.vars]),
        fun _ => allInside left (by simp [Metta.Bindings.vars])⟩
    · exact ⟨fun inside => (allOutside left (by simp [Metta.Bindings.vars]) inside).elim,
        fun inside => (allOutside right (by simp [Metta.Bindings.vars]) inside).elim⟩

theorem append {left right : Metta.Bindings}
    (hleft : BindingReadSupport support left) (hright : BindingReadSupport support right) :
    BindingReadSupport support (left++right) := by
  constructor
  · intro key value present inside
    exact (List.mem_append.mp present).elim
      (fun member => hleft.value key value member inside)
      (fun member => hright.value key value member inside)
  · intro leftKey rightKey present
    exact (List.mem_append.mp present).elim
      (fun member => hleft.equality leftKey rightKey member)
      (fun member => hright.equality leftKey rightKey member)

theorem class_mem (closed : BindingReadSupport support bindings)
    {start finish : String} (inside : support start)
    (member : finish ∈ Metta.Bindings.eqClass bindings start) : support finish := by
  obtain ⟨walk⟩ := mem_leaEqClass_iff_reachable.mp member
  clear member
  induction walk with
  | nil => exact inside
  | @cons first next last edge tail ih =>
    apply ih
    rcases edge.2 with forward | backward
    · exact (closed.equality first next (mem_leaEqualityEdges_iff.mp forward)).mp inside
    · exact (closed.equality next first (mem_leaEqualityEdges_iff.mp backward)).mpr inside

theorem representative (closed : BindingReadSupport support bindings)
    {key : String} (inside : support key) :
    support (Metta.Bindings.eqRepresentative bindings key) := by
  unfold Metta.Bindings.eqRepresentative
  cases ordered : Metta.Bindings.eqClassOrdered bindings key with
  | nil => exact inside
  | cons head tail =>
    apply closed.class_mem inside
    apply mem_leaEqClassOrdered_iff.mp
    rw [ordered]
    exact List.mem_cons_self

theorem class_value (closed : BindingReadSupport support bindings)
    {key : String} {value : Metta.Atom} (inside : support key)
    (member : value ∈ Metta.Bindings.classValues bindings key) :
    ∀ name ∈ value.vars, support name := by
  obtain ⟨owner,inClass,lookup⟩ := leaClassValue_mem_iff.mp member
  exact closed.value owner value (lookupVal_some_val_mem lookup) (closed.class_mem inside inClass)

theorem resolveAtomAux (closed : BindingReadSupport support bindings)
    (fuel : Nat) (visited : List String) (atom result : Metta.Atom)
    (inside : ∀ name ∈ atom.vars, support name)
    (resolved : Metta.Bindings.resolveAtomAux bindings fuel visited atom = some result) :
    ∀ name ∈ result.vars, support name := by
  induction fuel generalizing visited atom result with
  | zero => simp [Metta.Bindings.resolveAtomAux] at resolved
  | succ fuel ih =>
    cases atom with
    | sym symbol | gnd ground =>
      simp only [Metta.Bindings.resolveAtomAux,Option.some.injEq] at resolved
      subst result
      exact inside
    | var key =>
      have keyInside : support key := inside key (by simp [Metta.Atom.vars])
      have representativeInside : ∀ name ∈ (Metta.Atom.var
          (Metta.Bindings.eqRepresentative bindings key)).vars,support name := by
        simpa only [Metta.Atom.vars,List.mem_singleton,forall_eq] using closed.representative keyInside
      cases checked : (Metta.Bindings.eqClassOrdered bindings key).any visited.contains with
      | true => simp [Metta.Bindings.resolveAtomAux,checked] at resolved
      | false =>
        cases values : Metta.Bindings.classValues bindings key with
        | nil =>
          simp only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
            ↓reduceIte,values,Option.some.injEq] at resolved
          subst result
          exact representativeInside
        | cons value rest =>
          have valueInside := closed.class_value keyInside
            (show value ∈ Metta.Bindings.classValues bindings key by rw [values]; exact List.mem_cons_self)
          cases value with
          | sym symbol | gnd ground | expr children =>
            apply ih _ _ _ valueInside
            simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
              ↓reduceIte,values] using resolved
          | var other =>
            by_cases internal : (Metta.Bindings.eqClassOrdered bindings key).contains other = true
            · by_cases singleton : (Metta.Bindings.eqClassOrdered bindings key).length == 1
              · simp only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                  ↓reduceIte,values,internal,singleton] at resolved
                cases resolved
              · simp only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                  ↓reduceIte,values,internal,singleton,Option.some.injEq] at resolved
                subst result
                exact representativeInside
            · apply ih _ _ _ valueInside
              simpa only [Metta.Bindings.resolveAtomAux,checked,Bool.false_eq_true,
                ↓reduceIte,values,internal] using resolved
    | expr children =>
      have listInside : ∀ (source target : List Metta.Atom),
          (∀ child ∈ source,∀ name ∈ child.vars,support name) →
          source.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) = some target →
          ∀ child ∈ target,∀ name ∈ child.vars,support name := by
        intro source
        induction source with
        | nil =>
          intro target _ mapped
          simp at mapped
          subst target
          simp
        | cons head tail tailIH =>
          intro target inside mapped
          cases headResult : Metta.Bindings.resolveAtomAux bindings fuel visited head with
          | none => simp [List.mapM_cons,headResult] at mapped
          | some headValue =>
            cases tailResult : tail.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) with
            | none => simp [List.mapM_cons,headResult,tailResult] at mapped
            | some tailValues =>
              simp [List.mapM_cons,headResult,tailResult] at mapped
              subst target
              intro child present
              rcases List.mem_cons.mp present with equal | later
              · rw [equal]
                exact ih visited head headValue (inside head (by simp)) headResult
              · exact tailIH tailValues (fun item present => inside item (by simp [present]))
                  tailResult child later
      cases mapped : children.mapM (Metta.Bindings.resolveAtomAux bindings fuel visited) with
      | none => simp [Metta.Bindings.resolveAtomAux,mapped] at resolved
      | some outputs =>
        simp only [Metta.Bindings.resolveAtomAux,mapped,Option.some.injEq] at resolved
        subst result
        intro name mentioned
        simp only [Metta.Atom.vars,List.mem_flatten,List.mem_map] at mentioned
        obtain ⟨_,⟨child,present,rfl⟩,inChild⟩ := mentioned
        apply listInside children outputs ?_ mapped child present name inChild
        intro item present key inItem
        apply inside key
        simp only [Metta.Atom.vars,List.mem_flatten,List.mem_map]
        exact ⟨item.vars,⟨item,present,rfl⟩,inItem⟩

theorem resolve (closed : BindingReadSupport support bindings)
    {key : String} {result : Metta.Atom} (inside : support key)
    (resolved : Metta.Bindings.resolve bindings key = some result) :
    ∀ name ∈ result.vars,support name := by
  unfold Metta.Bindings.resolve at resolved
  dsimp only at resolved
  split at resolved
  · cases resolved
  · exact closed.resolveAtomAux _ [] (.var key) result
      (by simpa only [Metta.Atom.vars,List.mem_singleton,forall_eq] using inside) resolved

theorem instantiate (closed : BindingReadSupport support bindings)
    (atom : Metta.Atom) (inside : ∀ name ∈ atom.vars,support name) :
    ∀ name ∈ (Metta.instantiate bindings atom).vars,support name := by
  induction atom with
  | sym symbol | gnd ground =>
    simp [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Atom.vars]
  | var key =>
    cases resolved : Metta.Bindings.resolve bindings key with
    | none => simpa only [Metta.instantiate,Metta.Bindings.resolveAtom,resolved,
        Option.getD_none] using inside
    | some result =>
      simpa only [Metta.instantiate,Metta.Bindings.resolveAtom,resolved,
        Option.getD_some] using closed.resolve
          (inside key (by simp [Metta.Atom.vars])) resolved
  | expr children ih =>
    intro name mentioned
    simp only [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Atom.vars,
      List.mem_flatten,List.mem_map] at mentioned
    obtain ⟨_,⟨child,⟨original,present,rfl⟩,rfl⟩,inChild⟩ := mentioned
    apply ih original present ?_ name inChild
    intro key inOriginal
    apply inside key
    simp only [Metta.Atom.vars,List.mem_flatten,List.mem_map]
    exact ⟨original.vars,⟨original,present,rfl⟩,inOriginal⟩

theorem minimalResolveAtom (closed : BindingReadSupport support bindings)
    (fuel : Nat) (atom : Metta.Atom) (inside : ∀ name ∈ atom.vars,support name) :
    ∀ name ∈ (Metta.Minimal.resolveAtom bindings fuel atom).vars,support name := by
  induction fuel generalizing atom with
  | zero => exact inside
  | succ fuel ih =>
    rw [Metta.Minimal.resolveAtom]
    split
    · exact inside
    · exact ih _ (closed.instantiate atom inside)

/-- Public projection cannot introduce private names when stored equality and
value dependencies preserve the public region. Cyclic and inconsistent raw
records are allowed; refused recursive reads use their actual fallback. -/
theorem restrictBnd_vars_subset
    {support : List String} {bindings : Metta.Bindings}
    (closed : BindingReadSupport (fun key => key∈support) bindings)
    (scope : List String) (scopeInside : scope ⊆ support) :
    (Metta.Minimal.restrictBnd scope bindings).vars ⊆ support := by
  apply restrictBnd_vars_subset_of_readouts scope support bindings scopeInside
  intro key present
  exact closed.minimalResolveAtom _ (.var key)
    (by simpa only [Metta.Atom.vars,List.mem_singleton,forall_eq] using scopeInside present)

end BindingReadSupport
end BindingReadSupport

section IsolatedReadSupport
set_option autoImplicit true
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace IsolatedSolveFrame

/-- Interleaved solved private rows and caller rows induce the actual
resolver's public-support invariant. -/
theorem read_support (frame : IsolatedSolveFrame) {bindings : Metta.Bindings}
    (legal : frame.BindingsLegal bindings) : BindingReadSupport frame.caller bindings := by
  constructor
  · intro key value present keyInside name mentioned
    rcases legal (.val key value) present with ⟨privateKey,_⟩ | ⟨_,valueInside⟩
    · exact (frame.private_not_caller key privateKey keyInside).elim
    · exact valueInside name mentioned
  · intro left right present
    rcases legal (.eq left right) present with ⟨privateLeft,valueEq⟩ | ⟨leftInside,rightInside⟩
    · have leftOutside := frame.private_not_caller left privateLeft
      have rightOutside := frame.value_no_caller left privateLeft right
        (by rw [←valueEq]; simp [Metta.Atom.vars])
      exact ⟨fun inside => (leftOutside inside).elim,fun inside => (rightOutside inside).elim⟩
    · have rightCaller := rightInside right (by simp [Metta.Atom.vars])
      exact ⟨fun _ => rightCaller,fun _ => leftInside⟩

theorem projection_support (frame : IsolatedSolveFrame) {bindings : Metta.Bindings}
    (legal : frame.BindingsLegal bindings) (support scope : List String)
    (callerEq : ∀ key,frame.caller key ↔ key∈support) (scopeInside : scope ⊆ support) :
    (Metta.Minimal.restrictBnd scope bindings).vars ⊆ support := by
  have readClosed := frame.read_support legal
  have closed : BindingReadSupport (fun key => key∈support) bindings := by
    constructor
    · intro key value present keyInside name mentioned
      exact (callerEq name).mp (readClosed.value key value present ((callerEq key).mpr keyInside) name mentioned)
    · intro left right present
      rw [←callerEq left,←callerEq right]
      exact readClosed.equality left right present
  exact closed.restrictBnd_vars_subset scope scopeInside

end IsolatedSolveFrame
end IsolatedReadSupport

section OrientedHoleReadout
set_option autoImplicit true
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open private filter_insertLast from Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- An isolated oriented alias may occur repeatedly and interleaved with
unrelated aliases. Its public endpoint still precedes its private spelling. -/
theorem filter_eqVarsInOrder_oriented_pair
    (bindings : Metta.Bindings) (pattern binder : String) (distinct : pattern≠binder)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      (left=pattern ∧ right=binder) ∨
      (left≠pattern ∧ left≠binder ∧ right≠pattern ∧ right≠binder)) :
    (bindings.eqVarsInOrder).filter (fun key => key==binder || key==pattern) =
      @ite (List String) (Metta.BindingRel.eq pattern binder∈bindings) (Classical.propDecidable _) [binder,pattern] [] := by
  classical
  induction bindings with
  | nil => simp [Metta.Bindings.eqVarsInOrder]
  | cons relation rest ih =>
    have tail := ih (fun left right present => edges left right (by simp [present]))
    cases relation with
    | val key value => simpa only [leaEqVarsInOrder_cons_val,List.mem_cons,
        reduceCtorEq, false_or] using tail
    | eq left right =>
      rcases edges left right (by simp) with ⟨leftEq,rightEq⟩ | ⟨notPattern,notBinder,rightNotPattern,rightNotBinder⟩
      · subst left
        subst right
        rw [leaEqVarsInOrder_cons_eq,filter_insertLast,filter_insertLast,tail]
        by_cases present : Metta.BindingRel.eq pattern binder∈rest <;>
          simp [present,distinct,Ne.symm distinct]
      · rw [leaEqVarsInOrder_cons_eq,filter_insertLast,filter_insertLast,tail]
        simp [notPattern,notBinder,rightNotPattern,rightNotBinder,Ne.symm notPattern]

theorem eqClassOrdered_oriented_pair
    (bindings : Metta.Bindings) (pattern binder : String) (distinct : pattern≠binder)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      (left=pattern ∧ right=binder) ∨
      (left≠pattern ∧ left≠binder ∧ right≠pattern ∧ right≠binder))
    (present : Metta.BindingRel.eq pattern binder∈bindings) :
    bindings.eqClassOrdered binder=[binder,pattern] := by
  have classInside : ∀ key∈bindings.eqClass binder,key=binder ∨ key=pattern := by
    intro key member
    obtain ⟨walk⟩ := mem_leaEqClass_iff_reachable.mp member
    have keep : ∀ {start finish : String},
        (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Walk start finish →
        (start=binder ∨ start=pattern) → finish=binder ∨ finish=pattern := by
      intro start finish path
      induction path with
      | nil => exact id
      | @cons first next last edge tail ih =>
        intro inPair
        apply ih
        rcases edge.2 with forward | backward
        · rcases edges first next (mem_leaEqualityEdges_iff.mp forward) with
            ⟨_,rfl⟩ | ⟨firstNotPattern,firstNotBinder,_,_⟩
          · exact Or.inl rfl
          · exact (inPair.elim firstNotBinder firstNotPattern).elim
        · rcases edges next first (mem_leaEqualityEdges_iff.mp backward) with
            ⟨rfl,_⟩ | ⟨_,_,firstNotPattern,firstNotBinder⟩
          · exact Or.inr rfl
          · exact (inPair.elim firstNotBinder firstNotPattern).elim
    exact keep walk (Or.inl rfl)
  have classIff : ∀ key,key∈bindings.eqClass binder ↔ key=binder ∨ key=pattern := by
    intro key
    constructor
    · exact classInside key
    · intro member
      rcases member with same | same
      · rw [same]
        exact mem_leaEqClass_iff_reachable.mpr .rfl
      · rw [same]
        apply mem_leaEqClass_iff_reachable.mpr
        exact (show (EqualityClosure.edgeGraph (leaEqualityEdges bindings)).Adj binder pattern from
          ⟨Ne.symm distinct,Or.inr (mem_leaEqualityEdges_iff.mpr present)⟩).reachable
  have predicate : (fun key => (bindings.eqClass binder).contains key)=
      (fun key => key==binder || key==pattern) := by
    funext key
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem,Bool.or_eq_true,beq_iff_eq]
    exact classIff key
  unfold Metta.Bindings.eqClassOrdered
  rw [predicate,filter_eqVarsInOrder_oriented_pair bindings pattern binder distinct edges]
  simp [present]

/-- Direct lookup cannot select a value for an unassigned key, even if that
name occurs inside the values stored at other keys. -/
theorem lookupVal_none_of_no_assignment (bindings : Metta.Bindings) (key : String)
    (unassigned : ∀ value,Metta.BindingRel.val key value∉bindings) :
    bindings.lookupVal key=none := by
  cases lookup : bindings.lookupVal key with
  | none => rfl
  | some value => exact (unassigned value (lookupVal_some_val_mem lookup)).elim

theorem instantiate_oriented_unassigned_binder
    (bindings : Metta.Bindings) (pattern binder : String) (distinct : pattern≠binder)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      (left=pattern ∧ right=binder) ∨
      (left≠pattern ∧ left≠binder ∧ right≠pattern ∧ right≠binder))
    (unassigned : ∀ value,Metta.BindingRel.val binder value∉bindings)
    (patternValue : ∀ value,Metta.BindingRel.val pattern value∈bindings → value=.var binder) :
    Metta.instantiate bindings (.var binder)=.var binder := by
  have noBinder := lookupVal_none_of_no_assignment bindings binder unassigned
  by_cases edgePresent : Metta.BindingRel.eq pattern binder∈bindings
  · have classEq := eqClassOrdered_oriented_pair bindings pattern binder distinct edges edgePresent
    cases patternLookup : bindings.lookupVal pattern with
    | none =>
      simp [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Bindings.resolve,
        classEq,Metta.Bindings.classValues,noBinder,patternLookup,
        Metta.Bindings.resolutionFuel,Metta.Atom.size,Metta.Bindings.resolveAtomAux,
        Metta.Bindings.eqRepresentative,Nat.add_assoc]
    | some value =>
      have valueEq := patternValue value (lookupVal_some_val_mem patternLookup)
      subst value
      simp [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Bindings.resolve,
        classEq,Metta.Bindings.classValues,noBinder,patternLookup,
        Metta.Bindings.resolutionFuel,Metta.Atom.size,Metta.Bindings.resolveAtomAux,
        Metta.Bindings.eqRepresentative,Nat.add_assoc]
  · have noEdges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
        left≠binder ∧ right≠binder := by
      intro left right present
      rcases edges left right present with ⟨rfl,rfl⟩ | ⟨_,leftNotBinder,_,rightNotBinder⟩
      · exact (edgePresent present).elim
      · exact ⟨leftNotBinder,rightNotBinder⟩
    have classEq := Bindings.eqClassOrdered_singleton_of_no_edge noEdges
    simp [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Bindings.resolve,
      classEq,Metta.Bindings.classValues,noBinder]
end OrientedHoleReadout

section ClosedPrefixProjection
set_option autoImplicit true
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Unique direct keys make every stored private row agree with the frame's
actual lookup; this is a property of matcher-produced rows. -/
theorem lookupVal_of_mem_nodup_value_keys
    {bindings : Metta.Bindings} (keys : (bindingValueKeys bindings).Nodup)
    {key : String} {value : Metta.Atom} (present : .val key value∈bindings) :
    bindings.lookupVal key=some value := by
  induction bindings with
  | nil => cases present
  | cons relation rest ih =>
    cases relation with
    | eq left right =>
      have tail : .val key value∈rest := by simpa using present
      exact ih keys tail
    | val other atom =>
      have keyParts := List.nodup_cons.mp keys
      rcases List.mem_cons.mp present with same | tail
      · cases same
        simp [Metta.Bindings.lookupVal]
      · have different : key≠other := by
          intro same
          subst other
          apply keyParts.1
          exact mem_bindingValueKeys_iff.mpr ⟨value,tail⟩
        simpa [Metta.Bindings.lookupVal,different] using ih keyParts.2 tail

def closedValueFrame (privateRows caller : Metta.Bindings)
    (closed : ClosedValueBindings privateRows)
    (fresh : ∀ key∈bindingValueKeys privateRows,key∉caller.vars) : IsolatedSolveFrame where
  privateKey := fun key => key∈bindingValueKeys privateRows
  value := fun key => (privateRows.lookupVal key).getD (.sym "")
  caller := fun key => key∈caller.vars
  private_not_caller := fresh
  value_no_private := by
    intro key _ name member
    cases lookup : privateRows.lookupVal key with
    | none => simp [lookup,Metta.Atom.vars] at member
    | some value =>
      have empty := lookupVal_closed_value closed lookup
      simp [lookup,empty] at member
  value_no_caller := by
    intro key _ name member
    cases lookup : privateRows.lookupVal key with
    | none => simp [lookup,Metta.Atom.vars] at member
    | some value =>
      have empty := lookupVal_closed_value closed lookup
      simp [lookup,empty] at member

theorem closedValueFrame_private_legal (privateRows caller : Metta.Bindings)
    (closed : ClosedValueBindings privateRows)
    (fresh : ∀ key∈bindingValueKeys privateRows,key∉caller.vars)
    (keys : (bindingValueKeys privateRows).Nodup) :
    (closedValueFrame privateRows caller closed fresh).BindingsLegal privateRows := by
  intro relation present
  cases relation with
  | eq left right =>
    have impossible : Metta.BindingRel.eq left right ∈ ([] : Metta.Bindings) :=
      ValueBindings.eq_edge_mem_append (caller := []) closed.toValueBindings (by simpa using present)
    cases impossible
  | val key value =>
    left
    refine ⟨mem_bindingValueKeys_iff.mpr ⟨value,present⟩,?_⟩
    simp only [closedValueFrame,lookupVal_of_mem_nodup_value_keys keys present,Option.getD_some]

theorem IsolatedSolveFrame.legal_of_inside_caller (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings}
    (inside : ∀ name∈bindings.vars,frame.caller name) : frame.BindingsLegal bindings := by
  intro relation present
  cases relation with
  | val key value =>
    right
    constructor
    · exact inside key (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars]))
    · intro name mentioned
      exact inside name (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars,mentioned]))
  | eq left right =>
    right
    constructor
    · exact inside left (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars]))
    · intro name mentioned
      have same : name=right := by simpa [Metta.Atom.vars] using mentioned
      subst name
      exact inside right (bindingRelation_vars_subset present (by simp [Metta.Bindings.vars]))

/-- Actual reconciliation of a fresh closed matcher frame against arbitrary
retained caller work cannot expose private names in the caller projection.
Both the successful merge and its real right-hand fallback are covered. -/
theorem restrictBnd_merge_closed_prefix_support
    (privateRows caller partialBindings : Metta.Bindings) (scope : List String)
    (closed : ClosedValueBindings privateRows)
    (keys : (bindingValueKeys privateRows).Nodup)
    (fresh : ∀ key∈bindingValueKeys privateRows,key∉caller.vars)
    (partialInside : partialBindings.vars ⊆ caller.vars) (scopeInside : scope ⊆ caller.vars) :
    (Metta.Minimal.restrictBnd scope
      ((Metta.Bindings.merge partialBindings (privateRows++caller)).head?.getD (privateRows++caller))).vars ⊆
      caller.vars := by
  let frame := closedValueFrame privateRows caller closed fresh
  have privateLegal : frame.BindingsLegal privateRows :=
    closedValueFrame_private_legal privateRows caller closed fresh keys
  have callerLegal : frame.BindingsLegal caller := frame.legal_of_inside_caller (fun _ h => h)
  have partialLegal : frame.BindingsLegal partialBindings := frame.legal_of_inside_caller partialInside
  have combinedLegal : frame.BindingsLegal (privateRows++caller) := by
    intro relation present
    exact (List.mem_append.mp present).elim (privateLegal relation) (callerLegal relation)
  exact frame.projection_support
    (frame.merge_head_fallback_legal partialLegal combinedLegal combinedLegal)
    caller.vars scope (fun _ => Iff.rfl) scopeInside
end ClosedPrefixProjection

section LiteralHoleProjection
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A public hole which still reads as itself is omitted by projection.
Other public reads must avoid the hole, and no retained public equality may
attach it. The source record may still mention the hole in private rows. -/
theorem restrictBndRaw_omits_literal_hole
    (scope : List String) (bindings : Metta.Bindings) (hole : String)
    (literal : Metta.instantiate bindings (.var hole)=.var hole)
    (reads : ∀ key∈scope,key≠hole →
      hole∉(Metta.Minimal.resolveAtom bindings (bindings.length+1) (.var key)).vars)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      left∈scope → right∈scope → left≠hole ∧ right≠hole) :
    hole∉(Metta.Minimal.restrictBndRaw scope bindings).vars := by
  intro member
  rw [Metta.Minimal.restrictBndRaw,bindings_vars_append_iff] at member
  rcases member with solved | equality
  · simp only [Metta.Bindings.vars,List.mem_eraseDups,List.mem_flatMap] at solved
    obtain ⟨relation,present,mentioned⟩ := solved
    obtain ⟨key,keyPresent,projected⟩ := List.mem_filterMap.mp present
    by_cases same : key=hole
    · subst key
      simp [minimalResolveAtom_eq_of_instantiate_fixed bindings (.var hole) literal] at projected
    · have readAvoids := reads key keyPresent same
      cases value : Metta.Minimal.resolveAtom bindings (bindings.length+1) (.var key) with
      | sym symbol | gnd ground | expr children =>
        simp only [value,Option.some.injEq] at projected
        subst relation
        simp only [List.mem_cons] at mentioned
        rcases mentioned with equal | inValue
        · exact same equal.symm
        · exact readAvoids (by simpa only [value] using inValue)
      | var other =>
        simp only [value] at projected
        split at projected
        · cases projected
        · simp only [Option.some.injEq] at projected
          subst relation
          simp only [List.mem_cons,List.not_mem_nil,or_false] at mentioned
          rcases mentioned with equal | equal
          · exact same equal.symm
          · exact readAvoids (by simp [value,Metta.Atom.vars,equal])
  · simp only [Metta.Bindings.vars,List.mem_eraseDups,List.mem_flatMap] at equality
    obtain ⟨relation,present,mentioned⟩ := equality
    obtain ⟨original,selected⟩ := List.mem_filter.mp present
    cases relation with
    | val key value => contradiction
    | eq left right =>
      have selected : left∈scope ∧ right∈scope := by simpa using selected
      have avoids := edges left right original selected.1 selected.2
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mentioned
      exact mentioned.elim (fun same => avoids.1 same.symm) (fun same => avoids.2 same.symm)

theorem restrictBnd_omits_literal_hole
    (scope : List String) (bindings : Metta.Bindings) (hole : String)
    (literal : Metta.instantiate bindings (.var hole)=.var hole)
    (reads : ∀ key∈scope,key≠hole →
      hole∉(Metta.Minimal.resolveAtom bindings (bindings.length+1) (.var key)).vars)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      left∈scope → right∈scope → left≠hole ∧ right≠hole) :
    hole∉(Metta.Minimal.restrictBnd scope bindings).vars := by
  have rawAvoids := restrictBndRaw_omits_literal_hole scope bindings hole literal reads edges
  unfold Metta.Minimal.restrictBnd
  dsimp only
  cases head : (Metta.Bindings.merge [] (Metta.Minimal.restrictBndRaw scope bindings)).head? with
  | none => simpa only [head,Option.getD_none] using rawAvoids
  | some result =>
    simpa only [head,Option.getD_some] using
      merge_preserves_outside (List.mem_of_head? head) (by simp [Metta.Bindings.vars]) rawAvoids

/-- A scope formed from caller names and literal public holes drops every
unassigned hole after the actual canonical projection. This permits many
holes and arbitrary open caller bindings. -/
theorem restrictBnd_omits_literal_hole_of_caller_support
    (scope : List String) (bindings : Metta.Bindings) (hole : String)
    (caller : String → Prop) (support : BindingReadSupport caller bindings)
    (outside : ¬caller hole)
    (literal : Metta.instantiate bindings (.var hole)=.var hole)
    (scopeShape : ∀ key∈scope,caller key ∨ Metta.instantiate bindings (.var key)=.var key)
    (edges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
      left∈scope → right∈scope → left≠hole ∧ right≠hole) :
    hole∉(Metta.Minimal.restrictBnd scope bindings).vars := by
  apply restrictBnd_omits_literal_hole scope bindings hole literal ?_ edges
  intro key present different mentioned
  rcases scopeShape key present with inside | fixed
  · apply outside
    exact support.minimalResolveAtom _ (.var key)
      (by simpa [Metta.Atom.vars] using inside) hole mentioned
  · rw [minimalResolveAtom_eq_of_instantiate_fixed bindings (.var key) fixed] at mentioned
    have same : hole=key := by simpa [Metta.Atom.vars] using mentioned
    exact different same.symm
end LiteralHoleProjection

section IsolatedHoleReadout
set_option autoImplicit true
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace IsolatedSolveFrame

/-- A private frame with one oriented alias preserves that public hole as
the representative of its class, regardless of relation interleaving. -/
theorem single_alias_edges (frame : IsolatedSolveFrame)
    (pattern binder : String)
    (patternPrivate : frame.privateKey pattern)
    (binderOutside : ¬frame.caller binder)
    (onlyVariable : ∀ key,frame.privateKey key → ∀ other,
      frame.value key=.var other → key=pattern ∧ other=binder)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings) :
    ∀ left right,Metta.BindingRel.eq left right∈bindings →
      (left=pattern ∧ right=binder) ∨
      (left≠pattern ∧ left≠binder ∧ right≠pattern ∧ right≠binder) := by
  intro left right present
  rcases legal (.eq left right) present with ⟨privateLeft,valueEq⟩ | ⟨callerLeft,callerRight⟩
  · exact Or.inl (onlyVariable left privateLeft right valueEq.symm)
  · have rightInside := callerRight right (by simp [Metta.Atom.vars])
    right
    refine ⟨?_,?_,?_,?_⟩
    · intro same
      subst left
      exact frame.private_not_caller pattern patternPrivate callerLeft
    · intro same
      subst left
      exact binderOutside callerLeft
    · intro same
      subst right
      exact frame.private_not_caller pattern patternPrivate rightInside
    · intro same
      subst right
      exact binderOutside rightInside

theorem public_hole_unassigned (frame : IsolatedSolveFrame)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings)
    {key : String} (notPrivate : ¬frame.privateKey key) (notCaller : ¬frame.caller key) :
    ∀ value,Metta.BindingRel.val key value∉bindings := by
  intro value present
  rcases legal (.val key value) present with ⟨privateKey,_⟩ | ⟨callerKey,_⟩
  · exact notPrivate privateKey
  · exact notCaller callerKey

/-- Every public hole remains literal. The distinguished binder may have
many private aliases; other holes may occur inside stored templates. -/
theorem public_hole_literal (frame : IsolatedSolveFrame)
    (pattern binder : String)
    (patternPrivate : frame.privateKey pattern)
    (binderNotPrivate : ¬frame.privateKey binder)
    (binderNotCaller : ¬frame.caller binder)
    (patternValue : frame.value pattern=.var binder)
    (onlyVariable : ∀ key,frame.privateKey key → ∀ other,
      frame.value key=.var other → key=pattern ∧ other=binder)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings)
    (key : String) (notPrivate : ¬frame.privateKey key) (notCaller : ¬frame.caller key) :
    Metta.instantiate bindings (.var key)=.var key := by
  have edges := frame.single_alias_edges pattern binder patternPrivate binderNotCaller onlyVariable legal
  have noValue := frame.public_hole_unassigned legal notPrivate notCaller
  by_cases same : key=binder
  · subst key
    apply instantiate_oriented_unassigned_binder bindings pattern binder
      (by intro equal; subst pattern; exact binderNotPrivate patternPrivate) edges noValue
    intro value present
    rcases legal (.val pattern value) present with ⟨_,valueEq⟩ | ⟨callerPattern,_⟩
    · exact valueEq.trans patternValue
    · exact (frame.private_not_caller pattern patternPrivate callerPattern).elim
  · have noEdges : ∀ left right,Metta.BindingRel.eq left right∈bindings →
        left≠key ∧ right≠key := by
      intro left right present
      rcases legal (.eq left right) present with ⟨privateLeft,valueEq⟩ | ⟨callerLeft,callerRight⟩
      · have shape := onlyVariable left privateLeft right valueEq.symm
        refine ⟨fun equal => notPrivate (equal ▸ privateLeft),?_⟩
        rw [shape.2]
        exact Ne.symm same
      · refine ⟨fun equal => notCaller (equal ▸ callerLeft),?_⟩
        intro equal
        subst right
        exact notCaller (callerRight key (by simp [Metta.Atom.vars]))
    have classEq := Bindings.eqClassOrdered_singleton_of_no_edge noEdges
    have lookup := lookupVal_none_of_no_assignment bindings key noValue
    simp [Metta.instantiate,Metta.Bindings.resolveAtom,Metta.Bindings.resolve,
      classEq,Metta.Bindings.classValues,lookup]

/-- Actual public projection removes an unassigned hole from a legal
interleaved private frame, including canonical merge failure fallback. -/
theorem public_projection_omits_hole (frame : IsolatedSolveFrame)
    (pattern binder : String)
    (patternPrivate : frame.privateKey pattern)
    (binderNotPrivate : ¬frame.privateKey binder)
    (binderNotCaller : ¬frame.caller binder)
    (patternValue : frame.value pattern=.var binder)
    (onlyVariable : ∀ key,frame.privateKey key → ∀ other,
      frame.value key=.var other → key=pattern ∧ other=binder)
    {bindings : Metta.Bindings} (legal : frame.BindingsLegal bindings)
    (scope : List String) (scopePublic : ∀ key∈scope,¬frame.privateKey key)
    (hole : String) (holeNotPrivate : ¬frame.privateKey hole) (holeNotCaller : ¬frame.caller hole) :
    hole∉(Metta.Minimal.restrictBnd scope bindings).vars := by
  apply restrictBnd_omits_literal_hole_of_caller_support scope bindings hole frame.caller
    (frame.read_support legal) holeNotCaller
    (frame.public_hole_literal pattern binder patternPrivate binderNotPrivate binderNotCaller
      patternValue onlyVariable legal hole holeNotPrivate holeNotCaller)
  · intro key member
    by_cases inside : frame.caller key
    · exact Or.inl inside
    · exact Or.inr (frame.public_hole_literal pattern binder patternPrivate binderNotPrivate binderNotCaller
        patternValue onlyVariable legal key (scopePublic key member) inside)
  · intro left right present leftPublic rightPublic
    rcases legal (.eq left right) present with ⟨privateLeft,_⟩ | ⟨callerLeft,callerRight⟩
    · exact (scopePublic left leftPublic privateLeft).elim
    · refine ⟨fun equal => holeNotCaller (equal ▸ callerLeft),?_⟩
      intro equal
      subst right
      exact holeNotCaller (callerRight hole (by simp [Metta.Atom.vars]))

end IsolatedSolveFrame
end IsolatedHoleReadout

section LetReconciliationFrame
set_option autoImplicit true
open Metta
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-- The actual local-rule frame of a lazy `let`. Its fixed private slots
retain the public binder and arbitrarily many open template holes. -/
def letSolveFrame
    (pattern atomKey templateKey binder : String) (payload template : Metta.Atom)
    (caller : Metta.Bindings)
    (keys : [pattern,atomKey,templateKey].Nodup)
    (binderPrivate : binder∉[pattern,atomKey,templateKey])
    (privateFresh : ∀ key∈[pattern,atomKey,templateKey],key∉caller.vars)
    (binderFresh : binder∉caller.vars)
    (closed : payload.vars=[])
    (templateHoles : ∀ key∈template.vars,
      key∉[pattern,atomKey,templateKey] ∧ key∉caller.vars) : IsolatedSolveFrame where
  privateKey key := key∈[pattern,atomKey,templateKey]
  value key := if key=pattern then .var binder else if key=atomKey then payload else template
  caller key := key∈caller.vars
  private_not_caller := privateFresh
  value_no_private := by
    have distinct : pattern≠atomKey ∧ pattern≠templateKey ∧ atomKey≠templateKey := by
      simpa [List.nodup_cons,List.mem_cons,and_assoc] using keys
    intro key privateKey name mentioned
    simp only [List.mem_cons,List.not_mem_nil,or_false] at privateKey
    rcases privateKey with rfl | rfl | rfl
    · simp only [↓reduceIte,Metta.Atom.vars,List.mem_singleton] at mentioned
      simpa only [mentioned] using binderPrivate
    · simp [Ne.symm distinct.1,closed] at mentioned
    · simp only [Ne.symm distinct.2.1,Ne.symm distinct.2.2,↓reduceIte] at mentioned
      exact (templateHoles name mentioned).1
  value_no_caller := by
    have distinct : pattern≠atomKey ∧ pattern≠templateKey ∧ atomKey≠templateKey := by
      simpa [List.nodup_cons,List.mem_cons,and_assoc] using keys
    intro key privateKey name mentioned
    simp only [List.mem_cons,List.not_mem_nil,or_false] at privateKey
    rcases privateKey with rfl | rfl | rfl
    · simp only [↓reduceIte,Metta.Atom.vars,List.mem_singleton] at mentioned
      simpa only [mentioned] using binderFresh
    · simp [Ne.symm distinct.1,closed] at mentioned
    · simp only [Ne.symm distinct.2.1,Ne.symm distinct.2.2,↓reduceIte] at mentioned
      exact (templateHoles name mentioned).2

theorem letSolveFrame_private_rows_legal
    (pattern atomKey templateKey binder : String) (payload template : Metta.Atom)
    (caller : Metta.Bindings)
    (keys : [pattern,atomKey,templateKey].Nodup)
    (binderPrivate : binder∉[pattern,atomKey,templateKey])
    (privateFresh : ∀ key∈[pattern,atomKey,templateKey],key∉caller.vars)
    (binderFresh : binder∉caller.vars) (closed : payload.vars=[])
    (templateHoles : ∀ key∈template.vars,
      key∉[pattern,atomKey,templateKey] ∧ key∉caller.vars) :
    (letSolveFrame pattern atomKey templateKey binder payload template caller keys binderPrivate
      privateFresh binderFresh closed templateHoles).BindingsLegal
        [.eq pattern binder,.val atomKey payload,.val templateKey template] := by
  have distinct : pattern≠atomKey ∧ pattern≠templateKey ∧ atomKey≠templateKey := by
    simpa [List.nodup_cons,List.mem_cons,and_assoc] using keys
  intro relation present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl
  all_goals left
  · exact ⟨by simp [letSolveFrame],by simp [letSolveFrame]⟩
  · exact ⟨by simp [letSolveFrame],by simp [letSolveFrame,Ne.symm distinct.1]⟩
  · exact ⟨by simp [letSolveFrame],by
      simp [letSolveFrame,Ne.symm distinct.2.1,Ne.symm distinct.2.2]⟩

/-- Every real reconciled root, including fallback after a rejected raw merge,
retains the isolated local slot discipline. Caller records may be open,
inconsistent, duplicated or cyclic. -/
theorem letSolveFrame_reconciled_legal
    (pattern atomKey templateKey binder : String) (payload template : Metta.Atom)
    (caller partialBindings : Metta.Bindings)
    (keys : [pattern,atomKey,templateKey].Nodup)
    (binderPrivate : binder∉[pattern,atomKey,templateKey])
    (privateFresh : ∀ key∈[pattern,atomKey,templateKey],key∉caller.vars)
    (binderFresh : binder∉caller.vars) (closed : payload.vars=[])
    (templateHoles : ∀ key∈template.vars,
      key∉[pattern,atomKey,templateKey] ∧ key∉caller.vars)
    (partialInside : partialBindings.vars ⊆ caller.vars) :
    let frame := letSolveFrame pattern atomKey templateKey binder payload template caller keys
      binderPrivate privateFresh binderFresh closed templateHoles
    let root := [.eq pattern binder,.val atomKey payload,.val templateKey template]++caller
    frame.BindingsLegal ((Metta.Bindings.merge partialBindings root).head?.getD root) := by
  intro frame root
  have partialLegal : frame.BindingsLegal partialBindings :=
    frame.legal_of_inside_caller partialInside
  have callerLegal : frame.BindingsLegal caller := frame.legal_of_inside_caller (fun _ h => h)
  have localLegal := letSolveFrame_private_rows_legal pattern atomKey templateKey binder payload template
    caller keys binderPrivate privateFresh binderFresh closed templateHoles
  have rootLegal : frame.BindingsLegal root := by
    intro relation present
    exact (List.mem_append.mp present).elim (localLegal relation) (callerLegal relation)
  exact frame.merge_head_fallback_legal partialLegal rootLegal rootLegal

theorem letSolveFrame_only_variable
    (pattern atomKey templateKey binder : String) (payload template : Metta.Atom)
    (caller : Metta.Bindings)
    (keys : [pattern,atomKey,templateKey].Nodup)
    (binderPrivate : binder∉[pattern,atomKey,templateKey])
    (privateFresh : ∀ key∈[pattern,atomKey,templateKey],key∉caller.vars)
    (binderFresh : binder∉caller.vars) (closed : payload.vars=[])
    (templateHoles : ∀ key∈template.vars,
      key∉[pattern,atomKey,templateKey] ∧ key∉caller.vars)
    (templateNonvar : ∀ key,template≠.var key) :
    let frame := letSolveFrame pattern atomKey templateKey binder payload template caller keys
      binderPrivate privateFresh binderFresh closed templateHoles
    ∀ key,frame.privateKey key → ∀ other,frame.value key=.var other →
      key=pattern ∧ other=binder := by
  intro frame key privateKey other value
  have distinct : pattern≠atomKey ∧ pattern≠templateKey ∧ atomKey≠templateKey := by
    simpa [List.nodup_cons,List.mem_cons,and_assoc] using keys
  change key∈[pattern,atomKey,templateKey] at privateKey
  simp only [List.mem_cons,List.not_mem_nil,or_false] at privateKey
  rcases privateKey with rfl | rfl | rfl
  · have same : binder=other := by simpa only [frame,letSolveFrame,↓reduceIte,Metta.Atom.var.injEq] using value
    exact ⟨rfl,same.symm⟩
  · have impossible : payload=.var other := by simpa [frame,letSolveFrame,Ne.symm distinct.1] using value
    rw [impossible] at closed
    simp [Metta.Atom.vars] at closed
  · exact (templateNonvar other (by
      simpa [frame,letSolveFrame,Ne.symm distinct.2.1,Ne.symm distinct.2.2] using value)).elim

/-- Reconciliation and public projection do not bind the local result hole
or any later public hole in the same continuation. -/
theorem let_reconciled_projection_omits_public_hole
    (pattern atomKey templateKey binder : String) (payload template : Metta.Atom)
    (caller partialBindings : Metta.Bindings) (scope : List String)
    (keys : [pattern,atomKey,templateKey].Nodup)
    (binderPrivate : binder∉[pattern,atomKey,templateKey])
    (privateFresh : ∀ key∈[pattern,atomKey,templateKey],key∉caller.vars)
    (binderFresh : binder∉caller.vars) (closed : payload.vars=[])
    (templateHoles : ∀ key∈template.vars,
      key∉[pattern,atomKey,templateKey] ∧ key∉caller.vars)
    (templateNonvar : ∀ key,template≠.var key)
    (partialInside : partialBindings.vars ⊆ caller.vars)
    (scopePublic : ∀ key∈scope,key∉[pattern,atomKey,templateKey])
    (hole : String) (holePrivate : hole∉[pattern,atomKey,templateKey])
    (holeCaller : hole∉caller.vars) :
    let root : Metta.Bindings := [.eq pattern binder,.val atomKey payload,.val templateKey template]++caller
    hole∉(Metta.Minimal.restrictBnd scope
      ((Metta.Bindings.merge partialBindings root).head?.getD root)).vars := by
  intro root
  let frame := letSolveFrame pattern atomKey templateKey binder payload template caller keys
    binderPrivate privateFresh binderFresh closed templateHoles
  have legal := letSolveFrame_reconciled_legal pattern atomKey templateKey binder payload template caller
    partialBindings keys binderPrivate privateFresh binderFresh closed templateHoles partialInside
  exact frame.public_projection_omits_hole pattern binder (by simp [frame,letSolveFrame])
    binderPrivate binderFresh (by simp [frame,letSolveFrame])
    (letSolveFrame_only_variable pattern atomKey templateKey binder payload template caller keys
      binderPrivate privateFresh binderFresh closed templateHoles templateNonvar)
    legal scope scopePublic hole holePrivate holeCaller
end LetReconciliationFrame

section LetProjectionBoundary
set_option autoImplicit true
open Metta Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Public projection cannot invent a name absent from its actual input,
even when that name is requested by the source retention scope. -/
theorem restrictBnd_vars_subset_input (scope : List String) (bindings : Metta.Bindings) :
    (restrictBnd scope bindings).vars ⊆ bindings.vars := by
  intro key member
  by_contra outside
  exact restrictBnd_preserves_outside scope outside member

/-- This membership statement retains both the original operand syntax and
the incoming binding support. It does not replace a live source scope by the
variables remaining in an evaluated payload. -/
theorem expectedApplicationRetentionScope_mem_source_or_caller
    (incoming : Metta.Bindings) (args : List Metta.Atom) (key : String)
    (member : key∈expectedApplicationRetentionScope incoming args) :
    key∈args.flatMap Metta.Atom.vars ∨ key∈incoming.vars := by
  cases incoming with
  | nil => exact Or.inl member
  | cons relation rest =>
    change key∈args.flatMap Metta.Atom.vars ++ _ at member
    rcases List.mem_append.mp member with source | caller
    · exact Or.inl source
    · exact Or.inr (List.mem_filter.mp caller).1

/-- The original operand is closed, and all template holes are public.
After the real partial/root reconciliation, projection therefore discards
both the local binder and every later unassigned public hole. -/
theorem let_closed_source_projection_omits_hole
    (incoming partialBindings : Metta.Bindings) (binder : String)
    (sourcePayload payload template : Metta.Atom)
    (sourceClosed : sourcePayload.vars=[]) (closed : payload.vars=[])
    (fresh : binder∉incoming.vars)
    (holes : ∀ key∈template.vars,key∉incoming.vars)
    (templateNonvar : ∀ key,template≠.var key)
    (partialInside : partialBindings.vars ⊆ incoming.vars)
    (f : String→String) (injective : Function.Injective f)
    (separated : ∀ original∈["pattern","atom","template"],
      f original∉incoming.vars ∧ f original≠binder ∧
        f original∉payload.vars ∧ f original∉template.vars)
    (hole : String) (holeCaller : hole∉incoming.vars)
    (holePublic : hole=binder ∨ hole∈template.vars) :
    let scope := expectedApplicationRetentionScope incoming [.var binder,sourcePayload,template]
    let root : Metta.Bindings :=
      [.eq (f "pattern") binder,.val (f "atom") payload,.val (f "template") template]++incoming
    hole∉(restrictBnd scope ((Metta.Bindings.merge partialBindings root).head?.getD root)).vars := by
  intro scope root
  have keys : [f "pattern",f "atom",f "template"].Nodup := by
    simp [List.nodup_cons,injective.eq_iff]
  have names : ∀ key∈[f "pattern",f "atom",f "template"],
      ∃ original∈["pattern","atom","template"],key=f original := by
    intro key member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨"pattern",by simp,rfl⟩
    · exact ⟨"atom",by simp,rfl⟩
    · exact ⟨"template",by simp,rfl⟩
  have binderPrivate : binder∉[f "pattern",f "atom",f "template"] := by
    intro member
    obtain ⟨original,originalMember,equal⟩ := names binder member
    exact (separated original originalMember).2.1 equal.symm
  have privateFresh : ∀ key∈[f "pattern",f "atom",f "template"],key∉incoming.vars := by
    intro key member
    obtain ⟨original,originalMember,rfl⟩ := names key member
    exact (separated original originalMember).1
  have templateHoles : ∀ key∈template.vars,
      key∉[f "pattern",f "atom",f "template"] ∧ key∉incoming.vars := by
    intro key member
    refine ⟨?_,holes key member⟩
    intro privateMember
    obtain ⟨original,originalMember,rfl⟩ := names key privateMember
    exact (separated original originalMember).2.2.2 member
  have scopePublic : ∀ key∈scope,key∉[f "pattern",f "atom",f "template"] := by
    intro key member privateMember
    obtain ⟨original,originalMember,rfl⟩ := names key privateMember
    rcases expectedApplicationRetentionScope_mem_source_or_caller incoming
      [.var binder,sourcePayload,template] (f original) member with source | caller
    · simp only [List.flatMap_cons,List.flatMap_nil,Metta.Atom.vars,sourceClosed,
        List.nil_append,List.append_nil] at source
      have sourceSplit : f original=binder ∨ f original∈template.vars := by simpa using source
      rcases sourceSplit with equal | templateMember
      · exact (separated original originalMember).2.1 equal
      · exact (separated original originalMember).2.2.2 templateMember
    · exact (separated original originalMember).1 caller
  have holePrivate : hole∉[f "pattern",f "atom",f "template"] := by
    rcases holePublic with rfl | member
    · exact binderPrivate
    · exact (templateHoles hole member).1
  exact let_reconciled_projection_omits_public_hole (f "pattern") (f "atom") (f "template")
    binder payload template incoming partialBindings scope keys binderPrivate privateFresh fresh
    closed templateHoles templateNonvar partialInside scopePublic hole holePrivate holeCaller
end LetProjectionBoundary

section ClosedQueryProjection
set_option autoImplicit true
open Metta Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Entering a function result changes its stack, never its retained binding record. -/
theorem evalResult_bnd (prev : Stack) (value : Metta.Atom) (bindings : Metta.Bindings) :
    (evalResult prev value bindings).bnd=bindings := by
  unfold evalResult
  split <;> rfl

/-- Every accepted closed-query occurrence carries a fresh closed matcher
frame. Reconciliation with actual caller-supported partial work and public
projection therefore keeps only the caller's support. -/
theorem queryOpItem_closed_projection_support
    (prev : Stack) (target : Metta.Atom) (caller partialBindings : Metta.Bindings)
    (counter : Nat) (rule : Metta.Atom × Metta.Atom)
    (closed : target.vars=[]) (item : Item)
    (present : item∈queryOpItemsOfRule prev target caller counter rule)
    (scope : List String) (scopeInside : scope⊆caller.vars)
    (partialInside : partialBindings.vars⊆caller.vars) :
    (restrictBnd scope ((Metta.Bindings.merge partialBindings item.bnd).head?.getD item.bnd)).vars⊆
      caller.vars := by
  obtain ⟨matched,matchPresent,_loop,itemEq⟩ :=
    (mem_queryOpItemsOfRule_closed_frame_iff prev target caller counter rule closed item).mp present
  obtain ⟨matchClosed,unique,keys⟩ := matchAtoms_closed_footprint _ _ _ closed matchPresent
  rw [itemEq,evalResult_bnd]
  apply restrictBnd_merge_closed_prefix_support matched.reverse caller partialBindings scope
    matchClosed.reverse
  · rw [ValueBindings.bindingValueKeys_reverse matchClosed.toValueBindings]
    simpa only [List.nodup_reverse] using unique
  · intro key member
    rw [ValueBindings.bindingValueKeys_reverse matchClosed.toValueBindings,List.mem_reverse] at member
    exact queryOp_freshened_rule_avoids_caller prev target caller counter rule key
      (List.mem_append_left _ (keys key member))
  · exact partialInside
  · exact scopeInside

end ClosedQueryProjection

namespace BindingReadSupportControls
set_option autoImplicit true
open Metta Metta.Minimal
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def publicNames : List String := ["a","b","c"]
def interleaved : Metta.Bindings :=
  [.eq "private" "hole",.val "b" (.expr [.sym "F",.var "c"]),
   .val "private" (.sym "saved"),.eq "a" "b",.val "c" (.sym "Z")]

theorem interleaved_support : BindingReadSupport (fun key => key∈publicNames) interleaved := by
  constructor
  · intro key value present inside name mentioned
    simp only [interleaved,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with impossible | same | same | impossible | same
    · cases impossible
    · cases same
      have sameName : name="c" := by simpa [Metta.Atom.vars] using mentioned
      simp [sameName,publicNames]
    · cases same
      simp [publicNames] at inside
    · cases impossible
    · cases same
      simp [Metta.Atom.vars] at mentioned
  · intro left right present
    simp only [interleaved,List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with same | impossible | impossible | same | impossible
    · cases same
      simp [publicNames]
    · cases impossible
    · cases impossible
    · cases same
      simp [publicNames]
    · cases impossible

theorem projected_support :
    (restrictBnd publicNames interleaved).vars ⊆ publicNames :=
  interleaved_support.restrictBnd_vars_subset publicNames (fun _ h => h)

#guard instantiate interleaved (.var "a") == .expr [.sym "F",.sym "Z"]
#guard !(restrictBnd publicNames interleaved).vars.contains "private"
#guard !(restrictBnd publicNames interleaved).vars.contains "hole"

-- An explicit edge crossing the boundary invalidates the premise and leaks.
def crossing : Metta.Bindings := [.eq "a" "private"]
#guard (restrictBnd ["a"] crossing).vars.contains "private"

theorem crossing_not_closed : ¬BindingReadSupport (fun key => key="a") crossing := by
  intro closed
  have impossible := (closed.equality "a" "private" (by simp [crossing])).mp rfl
  simp at impossible

-- Acyclicity is distinct from consistency of an arbitrary raw record.
def inconsistent : Metta.Bindings :=
  [.val "a" (.sym "first"),.val "a" (.sym "second")]
#guard inconsistent.hasLoop == false
#guard instantiate inconsistent (.var "a") == .sym "first"

theorem inconsistent_has_no_model : ¬∃ valuation,LeaBindingSatisfied valuation inconsistent := by
  rintro ⟨valuation,values,_⟩
  have first := values "a" (.sym "first") (by simp [inconsistent])
  have second := values "a" (.sym "second") (by simp [inconsistent])
  have impossible := first.symm.trans second
  simp [applyClassSolution] at impossible

theorem inconsistent_still_preserves_support :
    BindingReadSupport (fun key => key="a") inconsistent := by
  apply BindingReadSupport.of_vars_subset
  intro name member
  simpa [inconsistent,Metta.Bindings.vars,Metta.Atom.vars] using member

end BindingReadSupportControls

namespace ClosedPrefixProjectionControls
set_option autoImplicit true
open Metta Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def privateRows : Metta.Bindings := [.val "private" (.expr [.sym "saved"])]
def caller : Metta.Bindings :=
  [.val "x" (.expr [.sym "F",.var "y"]),.val "y" (.sym "one")]
def partialBindings : Metta.Bindings := [.val "x" (.expr [.sym "F",.sym "one"])]
def reconciled := (Metta.Bindings.merge partialBindings (privateRows++caller)).head?.getD (privateRows++caller)

#guard !(Metta.Bindings.merge partialBindings (privateRows++caller)).isEmpty
#guard instantiate reconciled (.var "x") == .expr [.sym "F",.sym "one"]
#guard instantiate reconciled (.var "private") == .expr [.sym "saved"]
#guard !(restrictBnd caller.vars reconciled).vars.contains "private"

theorem actual_reconciliation_public_support :
    (restrictBnd caller.vars reconciled).vars ⊆ caller.vars := by
  apply restrictBnd_merge_closed_prefix_support privateRows caller partialBindings caller.vars
  · exact .val (by simp [Metta.Atom.vars]) .nil
  · decide
  · simp [privateRows,caller,bindingValueKeys,Metta.Bindings.vars,Metta.Atom.vars]
  · intro key present
    have same : key="x" := by simpa [partialBindings,Metta.Bindings.vars,Metta.Atom.vars] using present
    subst key
    simp [caller,Metta.Bindings.vars,Metta.Atom.vars]
  · exact fun _ h => h

def conflicting : Metta.Bindings := [.val "x" (.sym "first"),.val "x" (.sym "second")]
def fallback := (Metta.Bindings.merge conflicting (privateRows++conflicting)).head?.getD (privateRows++conflicting)
#guard (Metta.Bindings.merge conflicting (privateRows++conflicting)).isEmpty
#guard fallback == privateRows++conflicting
#guard !(restrictBnd conflicting.vars fallback).vars.contains "private"

theorem refused_merge_fallback_public_support :
    (restrictBnd conflicting.vars fallback).vars ⊆ conflicting.vars := by
  apply restrictBnd_merge_closed_prefix_support privateRows conflicting conflicting conflicting.vars
  · exact .val (by simp [Metta.Atom.vars]) .nil
  · decide
  · simp [privateRows,conflicting,bindingValueKeys,Metta.Bindings.vars,Metta.Atom.vars]
  · exact fun _ h => h
  · exact fun _ h => h

end ClosedPrefixProjectionControls

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
