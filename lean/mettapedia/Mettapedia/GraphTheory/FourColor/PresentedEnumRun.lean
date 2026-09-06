import Mettapedia.GraphTheory.FourColor.PresentedEnumSound

/-!
# Correctness of the enumerator, part two: the run over a vertex list

An assignment `σ'` extends `σ` when it agrees with `σ` on every assigned slot
(`Le`).  One vertex step produces exactly the extensions that assign the
vertex's three slots and nothing else new, and are proper at the vertex
(`mem_stepVertex_iff`); the run over a list produces exactly the extensions
assigning the slots of the listed vertices, proper at each of them
(`mem_runVertices_iff`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented

namespace PA

variable {N k : Nat} (x : Fin k → Fin 3)

/-- `σ'` extends `σ`: every assigned slot keeps its digit -/
def Le (σ σ' : PA N k) : Prop :=
  ∀ s, (σ.look x s).isSome → σ'.look x s = σ.look x s

theorem Le.refl (σ : PA N k) : Le x σ σ := fun _ _ => rfl

theorem Le.trans {σ₁ σ₂ σ₃ : PA N k} (h₁ : Le x σ₁ σ₂) (h₂ : Le x σ₂ σ₃) : Le x σ₁ σ₃ := by
  intro s hs
  rw [h₂ s (by rw [h₁ s hs]; exact hs), h₁ s hs]

theorem Le.isSome {σ σ' : PA N k} (h : Le x σ σ') {s : Slot N k} (hs : (σ.look x s).isSome) :
    (σ'.look x s).isSome := by
  rw [h s hs]; exact hs

/-- two assignments with the same `look` everywhere are equal -/
theorem ext_look {σ σ' : PA N k} (h : ∀ s, σ.look x s = σ'.look x s) : σ = σ' := by
  cases σ; cases σ'
  simp only [PA.mk.injEq]
  constructor
  · funext e; exact h (Slot.edge e)
  · funext i; exact h (Slot.out i)

theorem look_inp (σ : PA N k) (i : Fin k) : σ.look x (Slot.inp i) = some (x i) := rfl

theorem le_set (σ : PA N k) (s : Slot N k) (d : Fin 3) (hs : σ.look x s = none) :
    Le x σ (σ.set s d) := by
  intro s' hs'
  exact look_set_of_isSome x σ s s' d hs' hs

theorem look_set_isSome_iff (σ : PA N k) (s s' : Slot N k) (d : Fin 3) (hs : σ.look x s = none) :
    ((σ.set s d).look x s').isSome ↔ (σ.look x s').isSome ∨ s' = s := by
  by_cases h : s' = s
  · subst h
    rcases s' with e | i | i
    · simp [look_set_self x σ (Slot.edge e) d (fun _ h => by cases h)]
    · simp [look] at hs
    · simp [look_set_self x σ (Slot.out i) d (fun _ h => by cases h)]
  · rw [look_set_other x σ s s' d h]
    simp [h]

theorem properAt_of_le {σ σ' : PA N k} (h : Le x σ σ') {s0 s1 s2 : Slot N k}
    (hp : properAt x σ s0 s1 s2 = true) : properAt x σ' s0 s1 s2 = true := by
  rw [properAt_iff] at hp ⊢
  obtain ⟨a, b, c, h0, h1, h2, hab, hac, hbc⟩ := hp
  refine ⟨a, b, c, ?_, ?_, ?_, hab, hac, hbc⟩
  · rw [h s0 (by rw [h0]; rfl), h0]
  · rw [h s1 (by rw [h1]; rfl), h1]
  · rw [h s2 (by rw [h2]; rfl), h2]

/-- membership in a branch, as an extension statement -/
theorem mem_branch_le {σ σ' : PA N k} {s : Slot N k} (h : σ' ∈ branch x σ s) :
    Le x σ σ' ∧ ∀ s', (σ'.look x s').isSome ↔ (σ.look x s').isSome ∨ s' = s := by
  rw [mem_branch_iff] at h
  rcases h with ⟨hs, rfl⟩ | ⟨hs, d, rfl⟩
  · refine ⟨Le.refl x _, fun s' => ?_⟩
    constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hs
  · exact ⟨le_set x σ s d hs, fun s' => look_set_isSome_iff x σ s s' d hs⟩

/-- every extension that assigns exactly one more slot is a branch -/
theorem mem_branch_of {σ σ' : PA N k} {s : Slot N k} (hle : Le x σ σ')
    (hdom : ∀ s', (σ'.look x s').isSome ↔ (σ.look x s').isSome ∨ s' = s) :
    σ' ∈ branch x σ s := by
  rw [mem_branch_iff]
  by_cases hs : (σ.look x s).isSome
  · left
    refine ⟨hs, ?_⟩
    apply ext_look x
    intro s'
    by_cases h' : (σ.look x s').isSome
    · exact hle s' h'
    · have : ¬ (σ'.look x s').isSome := by
        rw [hdom]; rintro (h | rfl)
        · exact h' h
        · exact h' hs
      rw [Option.not_isSome_iff_eq_none] at h' this
      rw [h', this]
  · right
    have hnone : σ.look x s = none := Option.not_isSome_iff_eq_none.mp hs
    refine ⟨hnone, ?_⟩
    have hs' : (σ'.look x s).isSome := by rw [hdom]; exact Or.inr rfl
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs'
    refine ⟨d, ?_⟩
    apply ext_look x
    intro s'
    by_cases hss : s' = s
    · subst hss
      rw [hd]
      rcases s' with e | i | i
      · exact (look_set_self x σ (Slot.edge e) d (fun _ h => by cases h)).symm
      · simp [look] at hnone
      · exact (look_set_self x σ (Slot.out i) d (fun _ h => by cases h)).symm
    · rw [look_set_other x σ s s' d hss]
      by_cases h' : (σ.look x s').isSome
      · exact hle s' h'
      · have : ¬ (σ'.look x s').isSome := by
          rw [hdom]; rintro (h | h)
          · exact h' h
          · exact hss h
        rw [Option.not_isSome_iff_eq_none] at h' this
        rw [h', this]

end PA

/-! ## Restrictions of an assignment to a slot domain -/

namespace PA

variable {N k : Nat} (x : Fin k → Fin 3)

/-- the restriction of `σ'` to the slots satisfying `D` (in-ports are always readable) -/
def restrict (σ' : PA N k) (D : Slot N k → Bool) : PA N k :=
  ⟨fun e => if D (Slot.edge e) then σ'.e e else none,
    fun i => if D (Slot.out i) then σ'.o i else none⟩

theorem look_restrict_of {σ' : PA N k} {D : Slot N k → Bool} {s : Slot N k} (hD : D s = true) :
    (restrict σ' D).look x s = σ'.look x s := by
  cases s <;> simp [restrict, look, hD]

theorem look_restrict_of_not {σ' : PA N k} {D : Slot N k → Bool} {s : Slot N k}
    (hD : D s = false) (hs : ∀ i, s ≠ Slot.inp i) : (restrict σ' D).look x s = none := by
  cases s with
  | edge e => simp [restrict, look, hD]
  | inp i => exact absurd rfl (hs i)
  | out i => simp [restrict, look, hD]

theorem isSome_look_restrict {σ' : PA N k} {D : Slot N k → Bool}
    (hD : ∀ s, D s = true → (σ'.look x s).isSome) (hinp : ∀ i, D (Slot.inp i) = true)
    (s : Slot N k) : ((restrict σ' D).look x s).isSome ↔ D s = true := by
  by_cases h : D s = true
  · rw [look_restrict_of x h]; exact ⟨fun _ => h, fun _ => hD s h⟩
  · have h' : D s = false := by simpa using h
    rcases s with e | i | i
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)]; simp [h']
    · exact absurd (hinp i) (by simp [h'])
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)]; simp [h']

theorem le_restrict_restrict {σ' : PA N k} {D D' : Slot N k → Bool}
    (hDD : ∀ s, D s = true → D' s = true) :
    Le x (restrict σ' D) (restrict σ' D') := by
  intro s hs
  by_cases h : D s = true
  · rw [look_restrict_of x (hDD s h), look_restrict_of x h]
  · have h' : D s = false := by simpa using h
    rcases s with e | i | i
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)] at hs; simp at hs
    · rfl
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)] at hs; simp at hs

theorem le_restrict {σ' : PA N k} {D : Slot N k → Bool} : Le x (restrict σ' D) σ' := by
  intro s hs
  by_cases h : D s = true
  · rw [look_restrict_of x h]
  · have h' : D s = false := by simpa using h
    rcases s with e | i | i
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)] at hs; simp at hs
    · rfl
    · rw [look_restrict_of_not x h' (fun _ h => by cases h)] at hs; simp at hs

end PA

namespace Pres

open PA

variable {V N k : Nat} (P : Pres V N k) (x : Fin k → Fin 3)

/-- the slots of a vertex -/
def SlotOf (v : Fin V) (s : Slot N k) : Prop := s = P.tri v 0 ∨ s = P.tri v 1 ∨ s = P.tri v 2

/-- **one vertex step, exactly** -/
theorem mem_stepVertex_iff (v : Fin V) (σs : List (PA N k)) (σ' : PA N k) :
    σ' ∈ P.stepVertex x v σs ↔
      ∃ σ ∈ σs, Le x σ σ' ∧ (∀ s, (σ'.look x s).isSome ↔ (σ.look x s).isSome ∨ P.SlotOf v s) ∧
        properAt x σ' (P.tri v 0) (P.tri v 1) (P.tri v 2) = true := by
  unfold stepVertex
  simp only [List.mem_flatMap, List.mem_filter]
  constructor
  · rintro ⟨σ, hσ, σ1, h1, σ2, h2, h3, hp⟩
    obtain ⟨l1, d1⟩ := mem_branch_le x h1
    obtain ⟨l2, d2⟩ := mem_branch_le x h2
    obtain ⟨l3, d3⟩ := mem_branch_le x h3
    refine ⟨σ, hσ, (l1.trans x l2).trans x l3, fun s => ?_, hp⟩
    rw [d3, d2, d1]
    simp only [SlotOf]
    tauto
  · rintro ⟨σ, hσ, hle, hdom, hp⟩
    classical
    let D0 : Slot N k → Bool := fun s => (σ.look x s).isSome
    let D1 : Slot N k → Bool := fun s => D0 s || decide (s = P.tri v 0)
    let D2 : Slot N k → Bool := fun s => D1 s || decide (s = P.tri v 1)
    have hinp : ∀ i, D0 (Slot.inp i) = true := fun i => by simp [D0, look]
    have hD1 : ∀ s, D1 s = true → (σ'.look x s).isSome := fun s hs => by
      rw [hdom]
      simp only [D1, D0, Bool.or_eq_true, decide_eq_true_eq] at hs
      rcases hs with hs | hs
      · exact Or.inl hs
      · exact Or.inr (Or.inl hs)
    have hD2 : ∀ s, D2 s = true → (σ'.look x s).isSome := fun s hs => by
      simp only [D2, Bool.or_eq_true, decide_eq_true_eq] at hs
      rcases hs with hs | hs
      · exact hD1 s hs
      · rw [hdom]; exact Or.inr (Or.inr (Or.inl hs))
    have hinp1 : ∀ i, D1 (Slot.inp i) = true := fun i => by simp [D1, hinp i]
    have hinp2 : ∀ i, D2 (Slot.inp i) = true := fun i => by simp [D2, hinp1 i]
    refine ⟨σ, hσ, restrict σ' D1, ?_, restrict σ' D2, ?_, ?_, hp⟩
    · apply mem_branch_of x
      · intro s hs
        rw [look_restrict_of x (by simp [D1, D0, hs])]
        exact hle s hs
      · intro s
        rw [isSome_look_restrict x hD1 hinp1]
        simp [D1, D0]
    · apply mem_branch_of x
      · exact le_restrict_restrict x (fun s hs => by simp [D2, hs])
      · intro s
        rw [isSome_look_restrict x hD2 hinp2, isSome_look_restrict x hD1 hinp1]
        simp [D2]
    · apply mem_branch_of x
      · exact le_restrict x
      · intro s
        rw [isSome_look_restrict x hD2 hinp2, hdom]
        (simp only [D2, D1, D0, Bool.or_eq_true, decide_eq_true_eq, SlotOf]) <;> tauto

/-- the slots of a list of vertices -/
def SlotsOf (vs : List (Fin V)) (s : Slot N k) : Prop := ∃ v ∈ vs, P.SlotOf v s

/-- **the run over a vertex list, exactly** -/
theorem mem_runVertices_iff : ∀ (vs : List (Fin V)) (σs : List (PA N k)) (σ' : PA N k),
    σ' ∈ P.runVertices x vs σs ↔
      ∃ σ ∈ σs, Le x σ σ' ∧ (∀ s, (σ'.look x s).isSome ↔ (σ.look x s).isSome ∨ P.SlotsOf vs s) ∧
        ∀ v ∈ vs, properAt x σ' (P.tri v 0) (P.tri v 1) (P.tri v 2) = true
  | [], σs, σ' => by
    simp only [runVertices]
    constructor
    · intro h
      refine ⟨σ', h, Le.refl x σ', fun s => ?_, fun v hv => absurd hv List.not_mem_nil⟩
      constructor
      · exact Or.inl
      · rintro (h | ⟨v, hv, -⟩)
        · exact h
        · exact absurd hv List.not_mem_nil
    · rintro ⟨σ, hσ, hle, hdom, -⟩
      have : σ = σ' := by
        apply ext_look x
        intro s
        by_cases hs : (σ.look x s).isSome
        · exact (hle s hs).symm
        · have : ¬ (σ'.look x s).isSome := by
            rw [hdom]
            rintro (h | ⟨v, hv, -⟩)
            · exact hs h
            · exact absurd hv List.not_mem_nil
          rw [Option.not_isSome_iff_eq_none] at hs this
          rw [hs, this]
      rw [← this]; exact hσ
  | v :: vs, σs, σ' => by
    simp only [runVertices]
    rw [mem_runVertices_iff vs]
    constructor
    · rintro ⟨σ1, h1, hle, hdom, hp⟩
      rw [mem_stepVertex_iff] at h1
      obtain ⟨σ, hσ, hle0, hdom0, hp0⟩ := h1
      refine ⟨σ, hσ, hle0.trans x hle, fun s => ?_, ?_⟩
      · rw [hdom, hdom0]
        simp only [SlotsOf, List.mem_cons, exists_eq_or_imp]
        tauto
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact properAt_of_le x hle hp0
        · exact hp w hw
    · rintro ⟨σ, hσ, hle, hdom, hp⟩
      classical
      -- the intermediate assignment after `v`: restrict `σ'` to `σ`'s slots and `v`'s
      let D : Slot N k → Bool := fun s => (σ.look x s).isSome || decide (P.SlotOf v s)
      have hD : ∀ s, D s = true → (σ'.look x s).isSome := fun s hs => by
        rw [hdom]
        simp only [D, Bool.or_eq_true, decide_eq_true_eq] at hs
        rcases hs with hs | hs
        · exact Or.inl hs
        · exact Or.inr ⟨v, List.mem_cons_self, hs⟩
      have hinp : ∀ i, D (Slot.inp i) = true := fun i => by simp [D, look]
      refine ⟨restrict σ' D, ?_, le_restrict x, fun s => ?_, fun w hw => hp w (List.mem_cons_of_mem _ hw)⟩
      · rw [mem_stepVertex_iff]
        refine ⟨σ, hσ, ?_, fun s => ?_, ?_⟩
        · intro s hs
          rw [look_restrict_of x (by simp [D, hs])]
          exact hle s hs
        · rw [isSome_look_restrict x hD hinp]
          simp [D]
        · apply properAt_of_le x (le_restrict_restrict x (D' := D) (fun s hs => hs))
          rw [properAt_iff]
          have hp' := hp v (List.mem_cons_self)
          rw [properAt_iff] at hp'
          obtain ⟨a, b, c, h0, h1, h2, hab, hac, hbc⟩ := hp'
          refine ⟨a, b, c, ?_, ?_, ?_, hab, hac, hbc⟩
          · rw [look_restrict_of x (by simp [D, SlotOf]), h0]
          · rw [look_restrict_of x (by simp [D, SlotOf]), h1]
          · rw [look_restrict_of x (by simp [D, SlotOf]), h2]
      · rw [isSome_look_restrict x hD hinp, hdom]
        simp only [D, Bool.or_eq_true, decide_eq_true_eq, SlotsOf, List.mem_cons,
          exists_eq_or_imp]
        tauto

end Pres
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
