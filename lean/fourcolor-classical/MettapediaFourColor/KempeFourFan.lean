import MettapediaFourColor.KempeBoundaryFan
import MettapediaFourColor.KempeChromogramMatching
import MettapediaFourColor.KempeIntervalRepair

/-!
# Four-neighbour boundary insertion

Three consecutive boundary edges describe four old neighbours. A fresh
vertex can be inserted precisely when their colours omit one colour. The
joint trace relation is a split followed by two merges; thus it preserves
Kempe closure without forgetting the hidden boundary choices.
-/

namespace FourColor.KempeFourFan

open Color KempeBoundarySplit KempeBoundaryFan

def Related (a b c d e : Color) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧ e ≠ 0 ∧
    a + b = c + d + e ∧ a ≠ c ∧ a ≠ c + d
instance (a b c d e : Color) : Decidable (Related a b c d e) := by
  unfold Related; infer_instance

theorem junction : ∀ a b c d e : Color, Related a b c d e ↔
    ∃ k, a ≠ 0 ∧ k ≠ 0 ∧ a ≠ k ∧ d ≠ 0 ∧ k ≠ d ∧
      e ≠ 0 ∧ k + d ≠ e ∧ c = a + k ∧ b = (k + d) + e := by decide +kernel

def Fan (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ a b c d e t, et = a :: b :: t ∧ Related a b c d e ∧ P (c :: d :: e :: t)

def Transport (P : List Color → Prop) (n : ℕ) :=
  Rotate (KempeBoundaryMerge.Merge
    (KempeBoundaryMerge.Merge (Rotated (Split P)))) (n + 1)

theorem transport_closed {P : List Color → Prop} (h : KempeClosed P) (n : ℕ) :
    KempeClosed (Transport P n) :=
  closed_rotate (KempeBoundaryMerge.closed
    (KempeBoundaryMerge.closed (closed_rotated (KempeBoundarySplit.closed h)))) _

theorem transport_iff {P : List Color → Prop} {et : List Color} (n : ℕ)
    (hlen : et.length = n + 2) : Transport P n et ↔ Fan P et := by
  constructor
  · rintro ⟨es,hes,x,e,t,rfl,hx,he,hxe,k,d,ts,eq,hk,hd,hkd,old,hold,
      a,l,tail,rfl,ha,hl,hal,hp⟩
    simp only [List.cons.injEq] at eq
    obtain ⟨rfl,rfl⟩ := eq
    cases tail with
    | nil => simp at hold
    | cons q tail =>
      simp only [List.rotate_cons_succ,List.rotate_zero,List.cons_append,
        List.cons.injEq] at hold
      obtain ⟨rfl,hrest⟩ := hold
      cases tail with
      | nil =>
        simp only [List.nil_append,List.cons.injEq] at hrest
        obtain ⟨rfl,rfl,rfl⟩ := hrest
        have size := congrArg List.length hes
        simp only [List.length_rotate,List.length_cons,List.length_nil] at size
        omega
      | cons r rest =>
        simp only [List.cons_append,List.cons.injEq] at hrest
        obtain ⟨rfl,rfl,rfl⟩ := hrest
        have size := congrArg List.length hes
        simp only [List.length_rotate,List.length_cons,List.length_append,
          List.length_nil] at size
        have nt : rest.length = n := by omega
        have rot : (((l + q) + r) :: (rest ++ [a])).rotate (n + 1) =
            a :: ((l + q) + r) :: rest := by
          have h := List.rotate_append_length_eq (((l + q) + r) :: rest) [a]
          simpa [List.length_cons,nt] using h
        rw [rot] at hes
        exact ⟨a,(l+q)+r,a+l,q,r,rest,hes.symm,
          (junction _ _ _ _ _).mpr ⟨l,ha,hl,hal,hd,hkd,he,hxe,rfl,rfl⟩,hp⟩
  · rintro ⟨a,b,c,d,e,t,rfl,rel,hp⟩
    obtain ⟨k,ha,hk,hak,hd,hkd,he,hkde,rfl,rfl⟩ := (junction _ _ _ _ _).mp rel
    have nt : t.length = n := by simpa using hlen
    have hsum : k + d ≠ 0 := fun h => hkd (Color.add_eq_zero_iff.mp h)
    refine ⟨((k+d)+e) :: (t ++ [a]),?_,k+d,e,t++[a],rfl,hsum,he,hkde,
      k,d,e::(t++[a]),rfl,hk,hd,hkd,a::k::d::e::t,?_,a,k,d::e::t,
      rfl,ha,hk,hak,hp⟩
    · have h := List.rotate_append_length_eq (((k+d)+e) :: t) [a]
      simpa [List.length_cons,nt] using h
    · simp

theorem closed {P : List Color → Prop} (h : KempeClosed P) : KempeClosed (Fan P) := by
  rintro et ⟨a,b,c,d,e,t,rfl,rel,hp⟩
  have len : (a::b::t).length = t.length + 2 := by simp
  have member := (transport_iff t.length len).mpr ⟨a,b,c,d,e,t,rfl,rel,hp⟩
  obtain ⟨perms,gram,hm,all⟩ := transport_closed h t.length _ member
  refine ⟨?_,gram,hm,?_⟩
  · intro g
    exact (transport_iff t.length (by simp)).mp (perms g)
  · intro es hs
    have same := (matchg_length _ _ _ hs).symm.trans (matchg_length _ _ _ hm)
    exact (transport_iff t.length (same.trans len)).mp (all es hs)

/-- The four successive vertex colours omit a colour. -/
def Ready (a b c : Color) : Prop :=
  ∃ f : Color, f ≠ 0 ∧ f ≠ a ∧ f ≠ a+b ∧ f ≠ (a+b)+c
instance (a b c : Color) : Decidable (Ready a b c) := by
  unfold Ready; infer_instance

theorem not_ready : ∀ a b c : Color, a ≠ 0 → b ≠ 0 → c ≠ 0 →
    ¬ Ready a b c → a = c ∧ a ≠ b := by decide +kernel

private theorem switch_ready {n : ℕ} (w : Fin (n+4) → Color)
    (hz : ∀ i, w i ≠ 0) (same : w 0 = w 2) (sum : w 0 + w 1 = c1)
    (j : Fin (n+4)) (hj : j ≠ 1) :
    Ready (KempeIntervalRepair.switch w 1 j 0)
      (KempeIntervalRepair.switch w 1 j 1) (KempeIntervalRepair.switch w 1 j 2) := by
  have algebra : ∀ a b : Color, a ≠ 0 → b ≠ 0 → a+b=c1 →
      Ready (EdgePerm.e132 a) (EdgePerm.e132 b) a ∧
      Ready a (EdgePerm.e132 b) (EdgePerm.e132 a) ∧
      Ready a (EdgePerm.e132 b) a := by decide +kernel
  have h := algebra (w 0) (w 1) (hz 0) (hz 1) sum
  have h01 : (0 : Fin (n+4)) ≠ 1 := by
    intro eq
    have h := congrArg Fin.val eq
    change 0 % (n+4) = 1 % (n+4) at h
    simp only [Nat.zero_mod,Nat.mod_eq_of_lt (by omega : 1 < n+4)] at h
    contradiction
  have h02 : (0 : Fin (n+4)) ≠ 2 := by
    intro eq
    have h := congrArg Fin.val eq
    change 0 % (n+4) = 2 % (n+4) at h
    simp only [Nat.zero_mod,Nat.mod_eq_of_lt (by omega : 2 < n+4)] at h
    contradiction
  have h21 : (2 : Fin (n+4)) ≠ 1 := by
    intro eq
    have h := congrArg Fin.val eq
    change 2 % (n+4) = 1 % (n+4) at h
    simp only [Nat.mod_eq_of_lt (by omega : 2 < n+4),
      Nat.mod_eq_of_lt (by omega : 1 < n+4)] at h
    contradiction
  by_cases h0 : j = 0
  · subst j
    simpa [KempeIntervalRepair.switch,← same,h01,h02,h02.symm,h21] using h.1
  by_cases h2 : j = 2
  · subst j
    simpa [KempeIntervalRepair.switch,← same,h01,h02,h02.symm,h21] using h.2.1
  · simpa [KempeIntervalRepair.switch,Ne.symm h0,Ne.symm h2,← same,h01,h21] using h.2.2

/-- A single supplied component suffices to free a colour for four
consecutive neighbours. The exterior and all its hidden choices persist. -/
theorem prepare {n : ℕ} {P : List Color → Prop} (closed : KempeClosed P)
    (w : Fin (n+4) → Color) (hz : ∀ i, w i ≠ 0) (start : P (List.ofFn w)) :
    ∃ d : Fin (n+4) → Color, P (List.ofFn d) ∧ Ready (d 0) (d 1) (d 2) := by
  by_cases ready : Ready (w 0) (w 1) (w 2)
  · exact ⟨w,start,ready⟩
  obtain ⟨same,different⟩ := not_ready _ _ _ (hz 0) (hz 1) (hz 2) ready
  have fnz : w 0 + w 1 ≠ 0 := fun h => different (Color.add_eq_zero_iff.mp h)
  let g := EdgePerm.rotTo (w 0 + w 1)
  let c : Fin (n+4) → Color := fun i => g (w i)
  have nz : ∀ i, c i ≠ 0 := by
    intro i h
    apply hz i
    apply EdgePerm.apply_injective g
    simpa only [EdgePerm.apply_zero] using (show g (w i) = 0 from h)
  have sum : c 0 + c 1 = c1 := by
    rw [← EdgePerm.apply_add]
    exact EdgePerm.rotTo_apply_self fnz
  have ha : c 1 ≠ c1 := by
    intro h
    rw [h] at sum
    exact nz 0 (add_right_cancel (sum.trans (zero_add c1).symm))
  have retained : P (List.ofFn c) := by
    simpa only [List.map_ofFn,Function.comp_def,c] using (closed _ start).1 g
  obtain ⟨_,gram,matched,all⟩ := closed _ retained
  obtain ⟨mate,inv,_,fixed,exchange⟩ := KempeChromogramMatching.recover c gram matched
  have hj : mate 1 ≠ 1 := fun h => ha ((fixed 1).mp h)
  exact ⟨KempeIntervalRepair.switch c 1 (mate 1),all _ (exchange 1 ha),
    switch_ready c nz (congrArg g same) sum (mate 1) hj⟩

end FourColor.KempeFourFan
