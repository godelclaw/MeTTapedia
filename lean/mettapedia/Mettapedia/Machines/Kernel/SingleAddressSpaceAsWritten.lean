import Mettapedia.Machines.Kernel.SingleAddressSpace

/-!
# The single-address-space kernel as SexOS writes it

SexOS (github xirtus/sexos, revision 4a040a86) differs from `Kernel.step` in three requests:
- `reply` delivers to any domain named by number, whether or not it called the replier;
- `map` maps any physical frame, with protection key 0;
- user code can write the key register (`setKeys`, the WRPKRU instruction), since nothing keeps the
  instruction out of user code or user code out of writable memory.
Every domain's key register opens key 0.

Results:
- `asWritten_forged_reply`, `asWritten_foreign_store`, `asWritten_key_override`: each difference breaks
  a property `Kernel.step` guarantees (reply authenticity, memory integrity, key isolation);
- `asWritten_extra`: these are the only requests `Kernel.step` refuses and this kernel accepts;
- `asWritten_simulates`: on every request `Kernel.step` accepts, this kernel gives the same answer and
  the same rings, tables, owners, memory and reply slots. A program that never makes those three requests
  cannot tell the kernels apart.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel

variable {D : Type} [DecidableEq D]

/-- The step of the kernel as SexOS writes it. -/
def stepAsWritten (c : Config D) (s : State D) (d : D) : Op D → State D × Result D
  | .reply t w =>
      ({ s with pending := upd s.pending d ((s.pending d).erase t), slot := upd s.slot t (some w),
                answered := bump s.answered d t }, .done 0)
  | .map f => ({ s with maps := (f, 0) :: s.maps }, .done 0)
  | .setKeys k => ({ s with mask := upd s.mask d (upd (s.mask d) k true) }, .done 0)
  | op => step c s d op

/-- The only requests this kernel accepts and `Kernel.step` refuses: an unasked reply, mapping a frame
the domain does not own, and a user write of the key register. -/
theorem asWritten_extra (c : Config D) (s : State D) (d : D) (op : Op D)
    (h₁ : (step c s d op).2 = .refused) (h₂ : (stepAsWritten c s d op).2 ≠ .refused) :
    (∃ t w, op = .reply t w ∧ t ∉ s.pending d) ∨ (∃ f, op = .map f ∧ s.owner f ≠ some d) ∨
      (∃ k, op = .setKeys k) := by
  cases op with
  | reply t w =>
      left; refine ⟨t, w, rfl, fun hm => ?_⟩
      simp [step, hm] at h₁
  | map f =>
      right; left; refine ⟨f, rfl, fun ho => ?_⟩
      simp [step, ho] at h₁
  | setKeys k => right; right; exact ⟨k, rfl⟩
  | send => exact absurd h₁ h₂
  | listen => exact absurd h₁ h₂
  | alloc => exact absurd h₁ h₂
  | lend => exact absurd h₁ h₂
  | mapLent => exact absurd h₁ h₂
  | store => exact absurd h₁ h₂
  | load => exact absurd h₁ h₂

/-! ## Simulation on accepted requests -/

/-- The relation between a state of `Kernel.step` and one of the kernel as written: equal except that
the latter's mappings and key registers reach at least as much, and every register opens key 0. -/
structure Sim (ss sr : State D) : Prop where
  caps : sr.caps = ss.caps
  ring : sr.ring = ss.ring
  owner : sr.owner = ss.owner
  mem : sr.mem = ss.mem
  fresh : sr.fresh = ss.fresh
  pending : sr.pending = ss.pending
  slot : sr.slot = ss.slot
  heard : sr.heard = ss.heard
  answered : sr.answered = ss.answered
  mask_sub : ∀ d k, ss.mask d k = true → sr.mask d k = true
  mask_zero : ∀ d, sr.mask d 0 = true
  maps_sub : ∀ f k, (f, k) ∈ ss.maps → (f, k) ∈ sr.maps ∨ (f, 0) ∈ sr.maps

omit [DecidableEq D] in
theorem Sim.access {ss sr : State D} (h : Sim ss sr) {d : D} {f : Nat}
    (ha : canAccess ss d f = true) : canAccess sr d f = true := by
  obtain ⟨k, hm, hk⟩ := (canAccess_iff ss d f).mp ha
  rcases h.maps_sub f k hm with h' | h'
  · exact (canAccess_iff sr d f).mpr ⟨k, h', h.mask_sub d k hk⟩
  · exact (canAccess_iff sr d f).mpr ⟨0, h', h.mask_zero d⟩

/-- Both kernels add the same mapping. -/
theorem maps_sub_cons {A B : List (Nat × Nat)} (h : ∀ f k, (f, k) ∈ A → (f, k) ∈ B ∨ (f, 0) ∈ B)
    (m : Nat × Nat) : ∀ f k, (f, k) ∈ m :: A → (f, k) ∈ m :: B ∨ (f, 0) ∈ m :: B := by
  intro f k hm
  rcases List.mem_cons.mp hm with h' | h'
  · left; rw [h']; exact List.mem_cons_self
  · rcases h f k h' with h'' | h''
    · left; exact List.mem_cons_of_mem _ h''
    · right; exact List.mem_cons_of_mem _ h''

/-- On every request `Kernel.step` accepts, the kernel as written gives the same answer and keeps the
relation. -/
theorem asWritten_simulates (c : Config D) {ss sr : State D} (hs : Sim ss sr) (d : D) (op : Op D)
    (hacc : (step c ss d op).2 ≠ .refused) :
    (stepAsWritten c sr d op).2 = (step c ss d op).2 ∧
      Sim (step c ss d op).1 (stepAsWritten c sr d op).1 := by
  have hacs : ∀ {e : D} {f : Nat}, canAccess ss e f = true → canAccess sr e f = true :=
    fun h => hs.access h
  obtain ⟨caps, ring, owner, maps, mask, mem, fresh, pending, slot, heard, answered⟩ := ss
  obtain ⟨caps', ring', owner', maps', mask', mem', fresh', pending', slot', heard', answered'⟩ := sr
  obtain ⟨hc, hr, ho, hm, hf, hp, hsl, hh, ha, hms, hmz, hmp⟩ := hs
  simp only at hc hr ho hm hf hp hsl hh ha hms hmz hmp
  subst hc hr ho hm hf hp hsl hh ha
  -- the relation after a step that changes neither mappings nor registers
  have same : ∀ (s s' : State D), s'.caps = s.caps → s'.ring = s.ring → s'.owner = s.owner →
      s'.mem = s.mem → s'.fresh = s.fresh → s'.pending = s.pending → s'.slot = s.slot →
      s'.heard = s.heard → s'.answered = s.answered → s.maps = maps → s'.maps = maps' →
      s.mask = mask → s'.mask = mask' → Sim s s' := by
    intro s s' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rw [h12, h13]; exact hms, by rw [h13]; exact hmz,
      by rw [h10, h11]; exact hmp⟩
  cases op with
  | send sl w =>
      simp only [stepAsWritten, step] at hacc ⊢
      split
      · split
        · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
        · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  | listen =>
      simp only [stepAsWritten, step] at hacc ⊢
      split
      · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      · split
        · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
        · exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  | reply t w =>
      by_cases hmem : t ∈ pending' d
      · simp only [stepAsWritten, step, if_pos hmem]
        exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
      · simp [step, hmem] at hacc
  | alloc =>
      simp only [stepAsWritten, step]
      exact ⟨by trivial, same _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  | map f =>
      by_cases hown : owner' f = some d
      · simp only [stepAsWritten, step, if_pos hown]
        refine ⟨by trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hms, hmz, ?_⟩⟩
        intro f' k hmem
        rcases List.mem_cons.mp hmem with h' | h'
        · cases h'; right; exact List.mem_cons_self
        · rcases hmp f' k h' with h'' | h''
          · left; exact List.mem_cons_of_mem _ h''
          · right; exact List.mem_cons_of_mem _ h''
      · simp [step, hown] at hacc
  | lend sl dst =>
      simp only [stepAsWritten, step] at hacc ⊢
      split
      · split
        · exact ⟨by trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hms, hmz, maps_sub_cons hmp _⟩⟩
        · simp_all
      · simp_all
  | mapLent sl =>
      simp only [stepAsWritten, step] at hacc ⊢
      split
      · exact ⟨by trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hms, hmz, maps_sub_cons hmp _⟩⟩
      · simp_all
  | store f w =>
      simp only [stepAsWritten, step] at hacc ⊢
      split at hacc
      · rename_i hss
        rw [if_pos hss, if_pos (hacs hss)]
        exact ⟨by trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hms, hmz, hmp⟩⟩
      · exact absurd rfl hacc
  | load f =>
      simp only [stepAsWritten, step] at hacc ⊢
      split at hacc
      · rename_i hss
        rw [if_pos hss, if_pos (hacs hss)]
        exact ⟨by trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hms, hmz, hmp⟩⟩
      · exact absurd rfl hacc
  | setKeys k => exact absurd rfl hacc

/-! ## Counterexamples -/

/-- Two domains with keys 1 and 2 and rings of capacity 4. -/
def twoDomains : Config Bool where
  key := fun b => if b then 1 else 2
  key_inj := by intro a b; cases a <;> cases b <;> simp
  bound := 4

/-- A start for the kernel as written: no capabilities, nothing allocated, every key register opening key
0 and its own key, as SexOS assigns them. -/
def startAsWritten : State Bool :=
  { genesis twoDomains (fun _ _ => none) with mask := fun d k => k == 0 || k == twoDomains.key d }

/-- An unasked reply: `false` never heard from `true`, yet fills its reply slot. `Kernel.step` refuses the
same request. -/
theorem asWritten_forged_reply :
    let s := (stepAsWritten twoDomains startAsWritten false (.reply true 7)).1
    s.heard false true < s.answered false true ∧ s.slot true = some 7 ∧
      (step twoDomains startAsWritten false (.reply true 7)).2 = .refused := by
  decide

/-- `true` allocates and maps a frame for itself; `false`, which holds no capability to it, overwrites
it. Under `Kernel.step` the same requests leave the frame alone. -/
def foreignStoreOps : List (Bool × Op Bool) :=
  [(true, .alloc), (true, .map 0), (false, .store 0 9)]

/-- Run a list of requests. -/
def runOps {D : Type} [DecidableEq D] (k : Config D → State D → D → Op D → State D × Result D)
    (c : Config D) (s : State D) : List (D × Op D) → State D
  | [] => s
  | (d, op) :: rest => runOps k c (k c s d op).1 rest

theorem asWritten_foreign_store :
    let s := runOps stepAsWritten twoDomains startAsWritten foreignStoreOps
    s.owner 0 = some true ∧ (∀ sl w, s.caps false sl ≠ some ⟨.frame 0, w⟩) ∧ s.mem 0 = 9 ∧
      (runOps step twoDomains (genesis twoDomains (fun _ _ => none)) foreignStoreOps).mem 0 = 0 := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  have hcaps : (runOps stepAsWritten twoDomains startAsWritten foreignStoreOps).caps =
      fun _ _ => none := rfl
  intro sl w
  rw [hcaps]; simp

/-- A frame of `true` mapped under its own key 1. -/
def ownKeyFrame (mask : Bool → Nat → Bool) : State Bool :=
  { genesis twoDomains (fun _ _ => none) with
    owner := fun f => if f = 0 then some true else none, fresh := 1, maps := [(0, 1)], mask := mask }

/-- `false` writes the key register to open key 1 and overwrites `true`'s frame. Under `Kernel.step`
the register write is refused and so is the store. -/
theorem asWritten_key_override :
    let ops : List (Bool × Op Bool) := [(false, .setKeys 1), (false, .store 0 9)]
    (runOps stepAsWritten twoDomains
        (ownKeyFrame fun d k => k == 0 || k == twoDomains.key d) ops).mem 0 = 9 ∧
      (runOps step twoDomains (ownKeyFrame fun d k => k == twoDomains.key d) ops).mem 0 = 0 := by
  decide

/-- The start of `asWritten_key_override` for `Kernel.step` satisfies the invariant: the refusal is not
an artefact of a bad state. -/
theorem ownKeyFrame_good : Good twoDomains (ownKeyFrame fun d k => k == twoDomains.key d) where
  mask_own := by intro d k h; simpa [ownKeyFrame] using h
  maps_ok := by
    intro f k h d hk
    simp [ownKeyFrame] at h
    obtain ⟨rfl, rfl⟩ := h
    cases d <;> simp_all [twoDomains, ownKeyFrame]
  fresh_owner := by intro f hf; simp [ownKeyFrame] at hf ⊢; omega
  fresh_caps := by intro d n f w h; simp [ownKeyFrame, genesis] at h
  lent := by intro d n f w h; simp [ownKeyFrame, genesis] at h
  replies := by intro d e; simp [ownKeyFrame, genesis]

end Mettapedia.Machines.Kernel
