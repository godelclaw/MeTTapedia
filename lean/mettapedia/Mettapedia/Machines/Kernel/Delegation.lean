/-!
# Delegated authority: confinement, its exact reach, and revocation

Subjects hold capabilities to targets: other subjects (a capability with the grant flag to subject `b` lets
its holder pass capabilities to `b`) or objects. A holder may pass a copy of any capability it holds to a
subject it may grant to, keeping or dropping the copy's grant flag. Every copy records the capabilities it
was derived from, so revoking a capability removes everything derived from it.

The same model reads as a capability kernel (domains, endpoints, frames) or as agents delegating tools,
mailboxes and keys to each other.

Results:
- `Reachable.confined`: authority stays within `CanHold`, the closure of the genesis under passing on
  (authority confinement, as in the take-grant model and seL4's access-control proofs);
- `canHold_realized`: every `CanHold` fact is realized by some run, so `CanHold` is exactly the reachable
  authority;
- `revoke_removes_derived`, `revoke_keeps_unrelated`: revocation removes exactly the copies derived from
  the revoked capability.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.Delegation

/-- What a capability names. -/
inductive Target (S O : Type) where
  | subj (b : S)
  | obj (o : O)
  deriving DecidableEq, Repr

/-- A held capability: its identity, holder, target, grant flag, and the identities of the capabilities
it was copied from, nearest first. -/
structure Cap (S O : Type) where
  id : Nat
  holder : S
  target : Target S O
  grant : Bool
  ancestry : List Nat
  deriving DecidableEq, Repr

structure State (S O : Type) where
  caps : List (Cap S O)
  next : Nat

variable {S O : Type} [DecidableEq S] [DecidableEq O]

/-- A request: `pass a x g b` asks `a` to give `b` a copy of a capability to `x` with grant flag `g`;
`revoke a i` asks `a` to remove everything derived from its capability `i`. -/
inductive Op (S O : Type) where
  | pass (a : S) (x : Target S O) (g : Bool) (b : S)
  | revoke (a : S) (i : Nat)

/-- A capability of `a` to `x` whose grant flag covers `g`. -/
def source (st : State S O) (a : S) (x : Target S O) (g : Bool) : Option (Cap S O) :=
  st.caps.find? fun c => c.holder == a && c.target == x && (!g || c.grant)

/-- `a` may grant to `b`. -/
def mayGrant (st : State S O) (a b : S) : Bool :=
  st.caps.any fun c => c.holder == a && c.target == .subj b && c.grant

def step (st : State S O) : Op S O → State S O
  | .pass a x g b =>
      match source st a x g with
      | some c =>
          if mayGrant st a b then
            { caps := ⟨st.next, b, x, g, c.id :: c.ancestry⟩ :: st.caps, next := st.next + 1 }
          else st
      | none => st
  | .revoke a i =>
      if st.caps.any (fun c => c.id == i && c.holder == a) then
        { st with caps := st.caps.filter fun c => !(c.ancestry.contains i) }
      else st

def run (st : State S O) : List (Op S O) → State S O
  | [] => st
  | op :: rest => run (step st op) rest

/-- `a` holds a capability to `x` whose flag covers `g`. -/
def Holds (st : State S O) (a : S) (x : Target S O) (g : Bool) : Prop :=
  ∃ c ∈ st.caps, c.holder = a ∧ c.target = x ∧ (g = true → c.grant = true)

/-- The authority the genesis can ever give: closed under dropping the grant flag and under passing a
capability to a subject one may grant to. -/
inductive CanHold (st₀ : State S O) : S → Target S O → Bool → Prop
  | base {a x g} : Holds st₀ a x g → CanHold st₀ a x g
  | pass {a b x g} : CanHold st₀ a x g → CanHold st₀ a (.subj b) true → CanHold st₀ b x g

theorem source_spec {st : State S O} {a : S} {x : Target S O} {g : Bool} {c : Cap S O}
    (h : source st a x g = some c) : c ∈ st.caps ∧ c.holder = a ∧ c.target = x ∧ (g = true → c.grant = true) := by
  unfold source at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  refine ⟨hmem, h1, h2, ?_⟩
  intro hg; rcases h3 with h3 | h3
  · rw [hg] at h3; cases h3
  · exact h3

theorem source_of_holds {st : State S O} {a : S} {x : Target S O} {g : Bool} (h : Holds st a x g) :
    ∃ c, source st a x g = some c := by
  obtain ⟨c, hc, h1, h2, h3⟩ := h
  unfold source
  cases hf : st.caps.find? (fun c => c.holder == a && c.target == x && (!g || c.grant)) with
  | some c' => exact ⟨c', rfl⟩
  | none =>
      have := List.find?_eq_none.mp hf c hc
      simp only [h1, h2, beq_self_eq_true, Bool.true_and, Bool.or_eq_true,
        Bool.not_eq_true'] at this
      cases g with
      | false => simp at this
      | true => simp [h3 rfl] at this

theorem mayGrant_iff (st : State S O) (a b : S) : mayGrant st a b = true ↔ Holds st a (.subj b) true := by
  unfold mayGrant Holds
  constructor
  · intro h
    obtain ⟨c, hc, hp⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨c, hc, hp.1.1, hp.1.2, fun _ => hp.2⟩
  · rintro ⟨c, hc, h1, h2, h3⟩
    exact List.any_eq_true.mpr ⟨c, hc, by simp [h1, h2, h3 rfl]⟩

/-! ## Confinement -/

/-- One step keeps every held capability within `CanHold`. -/
theorem step_confined {st₀ st : State S O}
    (hconf : ∀ c ∈ st.caps, CanHold st₀ c.holder c.target c.grant) (op : Op S O) :
    ∀ c ∈ (step st op).caps, CanHold st₀ c.holder c.target c.grant := by
  cases op with
  | pass a x g b =>
      simp only [step]
      split
      · rename_i c hsrc
        split
        · rename_i hgr
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · obtain ⟨hmem, h1, h2, h3⟩ := source_spec hsrc
            have hc := hconf c hmem
            rw [h1, h2] at hc
            have hx : CanHold st₀ a x g := by
              cases g with
              | false =>
                  cases hcg : c.grant with
                  | false => rw [hcg] at hc; exact hc
                  | true =>
                      rw [hcg] at hc
                      -- dropping the flag: a held capability with flag covers the weaker request
                      exact weaken hc
              | true => rw [h3 rfl] at hc; exact hc
            obtain ⟨cg, hcg, g1, g2, g3⟩ := (mayGrant_iff st a b).mp hgr
            have hb := hconf cg hcg
            rw [g1, g2, g3 rfl] at hb
            exact CanHold.pass hx hb
          · exact hconf c' hc'
        · exact hconf
      · exact hconf
  | revoke a i =>
      simp only [step]
      split
      · intro c hc
        exact hconf c (List.mem_filter.mp hc).1
      · exact hconf
where
  /-- A capability held with the grant flag also counts without it. -/
  weaken {a : S} {x : Target S O} (h : CanHold st₀ a x true) : CanHold st₀ a x false := by
    generalize hg : true = g at h
    induction h with
    | base hh =>
        obtain ⟨c, hc, h1, h2, _⟩ := hh
        exact CanHold.base ⟨c, hc, h1, h2, fun h => absurd h (by simp)⟩
    | pass _ hb ih _ => exact CanHold.pass (ih hg) hb

/-- Over whole runs from a genesis, every held capability lies within `CanHold`. -/
theorem Reachable.confined (st₀ : State S O) (ops : List (Op S O)) :
    ∀ c ∈ (run st₀ ops).caps, CanHold st₀ c.holder c.target c.grant := by
  suffices h : ∀ st, (∀ c ∈ st.caps, CanHold st₀ c.holder c.target c.grant) →
      ∀ c ∈ (run st ops).caps, CanHold st₀ c.holder c.target c.grant by
    apply h
    intro c hc
    exact CanHold.base ⟨c, hc, rfl, rfl, fun h => h⟩
  induction ops with
  | nil => intro st h; exact h
  | cons op rest ih => intro st h; exact ih (step st op) (step_confined h op)

/-- Holding in a reachable state means holding within `CanHold`. -/
theorem holds_confined (st₀ : State S O) (ops : List (Op S O)) {a : S} {x : Target S O} {g : Bool}
    (h : Holds (run st₀ ops) a x g) : CanHold st₀ a x g := by
  obtain ⟨c, hc, h1, h2, h3⟩ := h
  have := Reachable.confined st₀ ops c hc
  rw [h1, h2] at this
  cases g with
  | false =>
      cases hcg : c.grant with
      | false => rw [hcg] at this; exact this
      | true => rw [hcg] at this; exact step_confined.weaken this
  | true => rw [h3 rfl] at this; exact this

/-! ## Every `CanHold` fact is realized -/

/-- Passing never removes a capability. -/
theorem holds_step_pass {st : State S O} {a b : S} {x : Target S O} {g : Bool} {a' : S}
    {x' : Target S O} {g' : Bool} (h : Holds st a' x' g') : Holds (step st (.pass a x g b)) a' x' g' := by
  obtain ⟨c, hc, h1, h2, h3⟩ := h
  simp only [step]
  split
  · split
    · exact ⟨c, List.mem_cons_of_mem _ hc, h1, h2, h3⟩
    · exact ⟨c, hc, h1, h2, h3⟩
  · exact ⟨c, hc, h1, h2, h3⟩

/-- Runs of passes only add capabilities. -/
def Passes (ops : List (Op S O)) : Prop := ∀ op ∈ ops, ∃ a x g b, op = Op.pass a x g b

theorem holds_run_passes {ops : List (Op S O)} (hp : Passes ops) {st : State S O} {a : S}
    {x : Target S O} {g : Bool} (h : Holds st a x g) : Holds (run st ops) a x g := by
  induction ops generalizing st with
  | nil => exact h
  | cons op rest ih =>
      obtain ⟨a', x', g', b', rfl⟩ := hp op List.mem_cons_self
      exact ih (fun o ho => hp o (List.mem_cons_of_mem _ ho)) (holds_step_pass h)

theorem run_append (st : State S O) (l₁ l₂ : List (Op S O)) : run st (l₁ ++ l₂) = run (run st l₁) l₂ := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons op rest ih => exact ih (step st op)

/-- A pass whose source and grant are both held gives the target subject the capability. -/
theorem holds_new_pass {st : State S O} {a b : S} {x : Target S O} {g : Bool} (hx : Holds st a x g)
    (hb : Holds st a (.subj b) true) : Holds (step st (.pass a x g b)) b x g := by
  obtain ⟨c, hc⟩ := source_of_holds hx
  have hm := (mayGrant_iff st a b).mpr hb
  simp only [step, hc, hm, if_true]
  exact ⟨_, List.mem_cons_self, rfl, rfl, fun h => h⟩

/-- A pass is monotone in what is held before it. -/
theorem step_pass_mono {st st' : State S O} (hsub : ∀ a x g, Holds st a x g → Holds st' a x g)
    (a : S) (x : Target S O) (g : Bool) (b : S) :
    ∀ a' x' g', Holds (step st (.pass a x g b)) a' x' g' → Holds (step st' (.pass a x g b)) a' x' g' := by
  intro a' x' g' h
  simp only [step] at h
  split at h
  · rename_i c hsrc
    split at h
    · rename_i hgr
      obtain ⟨c', hc', h1, h2, h3⟩ := h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · simp only at h1 h2 h3
        subst h1 h2
        obtain ⟨hmem, k1, k2, k3⟩ := source_spec hsrc
        have hx : Holds st' a x g := hsub _ _ _ ⟨c, hmem, k1, k2, k3⟩
        have hb : Holds st' a (.subj b) true := hsub _ _ _ ((mayGrant_iff st a b).mp hgr)
        obtain ⟨c2, hc2, e1, e2, e3⟩ := holds_new_pass hx hb
        exact ⟨c2, hc2, e1, e2, fun hg' => e3 (h3 hg')⟩
      · exact holds_step_pass (hsub _ _ _ ⟨c', hc', h1, h2, h3⟩)
    · exact holds_step_pass (hsub _ _ _ h)
  · exact holds_step_pass (hsub _ _ _ h)

/-- Runs of passes are monotone in what is held at their start. -/
theorem run_passes_mono {ops : List (Op S O)} (hp : Passes ops) {st st' : State S O}
    (hsub : ∀ a x g, Holds st a x g → Holds st' a x g) :
    ∀ a x g, Holds (run st ops) a x g → Holds (run st' ops) a x g := by
  induction ops generalizing st st' with
  | nil => exact hsub
  | cons op rest ih =>
      obtain ⟨a, x, g, b, rfl⟩ := hp op List.mem_cons_self
      exact ih (fun o ho => hp o (List.mem_cons_of_mem _ ho)) (step_pass_mono hsub a x g b)

/-- Every `CanHold` fact is realized by a run of passes from the genesis. -/
theorem canHold_realized {st₀ : State S O} {a : S} {x : Target S O} {g : Bool} (h : CanHold st₀ a x g) :
    ∃ ops, Passes ops ∧ Holds (run st₀ ops) a x g := by
  induction h with
  | base hh => exact ⟨[], fun _ h => absurd h List.not_mem_nil, hh⟩
  | @pass a b x g _ _ ih₁ ih₂ =>
      obtain ⟨o₁, p₁, h₁⟩ := ih₁
      obtain ⟨o₂, p₂, h₂⟩ := ih₂
      refine ⟨o₁ ++ o₂ ++ [.pass a x g b], ?_, ?_⟩
      · intro op hop
        rcases List.mem_append.mp hop with hop | hop
        · rcases List.mem_append.mp hop with hop | hop
          · exact p₁ op hop
          · exact p₂ op hop
        · rw [List.mem_singleton.mp hop]; exact ⟨a, x, g, b, rfl⟩
      · rw [run_append, run_append]
        have hx : Holds (run (run st₀ o₁) o₂) a x g := holds_run_passes p₂ h₁
        have hb : Holds (run (run st₀ o₁) o₂) a (.subj b) true :=
          run_passes_mono p₂ (fun _ _ _ hh => holds_run_passes p₁ hh) _ _ _ h₂
        exact holds_new_pass hx hb

/-- `CanHold` is exactly the authority reachable by passing from the genesis. -/
theorem canHold_iff (st₀ : State S O) (a : S) (x : Target S O) (g : Bool) :
    CanHold st₀ a x g ↔ ∃ ops, Holds (run st₀ ops) a x g :=
  ⟨fun h => (canHold_realized h).imp fun _ h => h.2, fun ⟨ops, h⟩ => holds_confined st₀ ops h⟩

/-! ## Revocation -/

/-- After `a` revokes its capability `i`, no capability derived from `i` remains. -/
theorem revoke_removes_derived (st : State S O) (a : S) (i : Nat) :
    ∀ c ∈ (step st (.revoke a i)).caps, st.caps.any (fun c => c.id == i && c.holder == a) = true →
      i ∉ c.ancestry := by
  intro c hc hheld
  simp only [step, hheld, if_true] at hc
  have := (List.mem_filter.mp hc).2
  simpa [List.contains_iff_mem] using this

/-- Revocation keeps every capability not derived from the revoked one. -/
theorem revoke_keeps_unrelated (st : State S O) (a : S) (i : Nat) (c : Cap S O) (hc : c ∈ st.caps)
    (hi : i ∉ c.ancestry) : c ∈ (step st (.revoke a i)).caps := by
  simp only [step]
  split
  · exact List.mem_filter.mpr ⟨hc, by simpa [List.contains_iff_mem] using hi⟩
  · exact hc

end Mettapedia.Machines.Kernel.Delegation
