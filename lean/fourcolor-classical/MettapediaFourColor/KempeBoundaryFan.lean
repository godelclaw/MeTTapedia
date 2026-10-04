import MettapediaFourColor.KempeBoundaryMerge

/-!
# Repair transport through a two-triangle boundary fan

The old and new middle vertices are adjacent and share two boundary
neighbours. Replacing the old middle port by the new one preserves the
sum of the two edge colours, while changing both of them. The complete
joint relation is symmetric. Its closure follows by composing the existing
split, rotation and merge laws, retaining the same exterior predicate.
-/

namespace FourColor.KempeBoundaryFan

open Color KempeBoundarySplit

/-- The four incident boundary edges and the shared internal edge. -/
def Related (a b c d : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ a + b = c + d ∧ a ≠ c

instance (a b c d : Color) : Decidable (Related a b c d) := by
  unfold Related; infer_instance

theorem related_symm {a b c d : Color} (h : Related a b c d) : Related c d a b :=
  ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩

theorem related_junction : ∀ a b c d : Color, Related a b c d ↔
    ∃ k, a ≠ 0 ∧ k ≠ 0 ∧ a ≠ k ∧ d ≠ 0 ∧ k ≠ d ∧
      b = k + d ∧ c = a + k := by decide +kernel

def Fan (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ a b c d t, et = a :: b :: t ∧ Related a b c d ∧ P (c :: d :: t)

def Rotate (P : List Color → Prop) (n : ℕ) (et : List Color) : Prop :=
  ∃ es, es.rotate n = et ∧ P es

theorem closed_rotate {P : List Color → Prop} (h : KempeClosed P) (n : ℕ) :
    KempeClosed (Rotate P n) := by
  induction n with
  | zero =>
    have eq : Rotate P 0 = P := by
      funext et
      simp [Rotate]
    rw [eq]
    exact h
  | succ n ih =>
    have eq : Rotate P (n + 1) = Rotated (Rotate P n) := by
      funext et
      apply propext
      constructor
      · rintro ⟨es, rfl, hp⟩
        exact ⟨es.rotate n, List.rotate_rotate es n 1, es, rfl, hp⟩
      · rintro ⟨es, rfl, bs, rfl, hp⟩
        exact ⟨bs, (List.rotate_rotate bs n 1).symm, hp⟩
    rw [eq]
    exact closed_rotated ih

/-- A fan consists of two existing junction operations with their shared port. -/
def Transport (P : List Color → Prop) (n : ℕ) :=
  Rotate (KempeBoundaryMerge.Merge (Rotated (Split P))) (n + 1)

theorem transport_closed {P : List Color → Prop} (h : KempeClosed P) (n : ℕ) :
    KempeClosed (Transport P n) :=
  closed_rotate (KempeBoundaryMerge.closed (closed_rotated (KempeBoundarySplit.closed h))) _

theorem transport_iff {P : List Color → Prop} {et : List Color} (n : ℕ)
    (hlen : et.length = n + 2) : Transport P n et ↔ Fan P et := by
  constructor
  · rintro ⟨es, hes, x, y, zs, rfl, hx, hy, hxy, old, hold,
      a, k, ts, rfl, ha, hk, hak, hp⟩
    cases ts with
    | nil =>
      simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append,
        List.nil_append, List.cons.injEq] at hold
      obtain ⟨rfl, rfl, rfl⟩ := hold
      have size := congrArg List.length hes
      simp only [List.length_rotate, List.length_cons, List.length_nil] at size
      omega
    | cons d t =>
      simp only [List.rotate_cons_succ, List.rotate_zero, List.cons_append,
        List.cons.injEq] at hold
      obtain ⟨rfl, rfl, rfl⟩ := hold
      have size := congrArg List.length hes
      simp only [List.length_rotate, List.length_cons, List.length_append,
        List.length_nil] at size
      have nt : t.length = n := by omega
      have rot : ((k + d) :: (t ++ [a])).rotate (n + 1) = a :: (k + d) :: t := by
        have h := List.rotate_append_length_eq ((k + d) :: t) [a]
        simpa [List.length_cons, nt] using h
      rw [rot] at hes
      refine ⟨a, k + d, a + k, d, t, hes.symm, ?_, hp⟩
      exact (related_junction _ _ _ _).mpr ⟨k, ha, hk, hak, hy, hxy, rfl, rfl⟩
  · rintro ⟨a, b, c, d, t, rfl, rel, hp⟩
    obtain ⟨k, ha, hk, hak, hd, hkd, rfl, rfl⟩ := (related_junction _ _ _ _).mp rel
    have nt : t.length = n := by simpa using hlen
    refine ⟨(k + d) :: (t ++ [a]), ?_, k, d, t ++ [a], rfl, hk, hd, hkd,
      a :: k :: d :: t, ?_, a, k, d :: t, rfl, ha, hk, hak, hp⟩
    · have h := List.rotate_append_length_eq ((k + d) :: t) [a]
      simpa [List.length_cons, nt] using h
    · simp

/-- The transformation preserves every closed exterior, not only its marginals. -/
theorem closed {P : List Color → Prop} (h : KempeClosed P) : KempeClosed (Fan P) := by
  rintro et start
  obtain ⟨a, b, c, d, t, rfl, rel, hp⟩ := start
  have len : (a :: b :: t).length = t.length + 2 := by simp
  have member := (transport_iff t.length len).mpr ⟨a, b, c, d, t, rfl, rel, hp⟩
  obtain ⟨perms, gram, hmatch, all⟩ := transport_closed h t.length _ member
  refine ⟨?_, gram, hmatch, ?_⟩
  · intro g
    exact (transport_iff t.length (by simp)).mp (perms g)
  · intro es hs
    have same : es.length = (a :: b :: t).length :=
      (matchg_length _ _ _ hs).symm.trans (matchg_length _ _ _ hmatch)
    exact (transport_iff t.length (same.trans len)).mp (all es hs)

/-- A successful old repair lifts through the fan with the same exterior. -/
theorem repair {P Q : List Color → Prop}
    (reconstruct : ∀ a b c d t, Related a b c d → P (c :: d :: t) → Q (a :: b :: t))
    {a b c d : Color} (t : List Color) (rel : Related a b c d)
    (old : KempeCoclosure P (c :: d :: t)) : KempeCoclosure Q (a :: b :: t) := by
  intro outside hout start
  obtain ⟨et, hp, x, y, u, v, tail, rfl, relation, ho⟩ :=
    old (Fan outside) (closed hout) ⟨c, d, a, b, t, rfl, related_symm rel, start⟩
  exact ⟨_, reconstruct u v x y tail (related_symm relation) hp, ho⟩

theorem repairs {P : List Color → Prop} {n : ℕ} (hn : 2 ≤ n)
    (old : Repairs P n) : Repairs (Fan P) n := by
  intro et len nz sum
  cases et with
  | nil => simp at len; omega
  | cons a et => cases et with
    | nil => simp at len; omega
    | cons b t =>
      have ha : a ≠ 0 := fun h => nz (by simp [h])
      have hb : b ≠ 0 := fun h => nz (by simp [h])
      obtain ⟨c, d, rel⟩ : ∃ c d, Related a b c d := by
        revert ha hb; cases a <;> cases b <;> decide
      apply repair (fun a b c d t h hp => ⟨a,b,c,d,t,rfl,h,hp⟩) t rel
      apply old
      · simpa using len
      · simpa only [List.mem_cons, not_or, ne_eq, eq_comm] using
          And.intro rel.2.2.1 (And.intro rel.2.2.2.1
            (fun h => nz (by simp [h])))
      · simpa only [List.sum_cons, ← add_assoc, ← rel.2.2.2.2.1] using sum

end FourColor.KempeBoundaryFan
