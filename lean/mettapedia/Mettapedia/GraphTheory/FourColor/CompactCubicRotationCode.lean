import Mettapedia.GraphTheory.FourColor.BoundedSphericalBaseAudit

/-!
# Removing the redundant permutations from bounded cubic rotation codes

Valid incidence determines the edge flip uniquely. A cyclic rotation of the
three positions at each vertex has only two choices. The compact code stores
incidence and one orientation bit per vertex; decoding reconstructs every
valid rotation code exactly, without quotienting away the supplied embedding.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace

def Partner {n m : Nat} (code : Code n m) (d e : Position n) : Prop :=
  d.1 ≠ e.1 ∧ code e.1 e.2 = code d.1 d.2

instance {n m : Nat} (code : Code n m) (d e : Position n) :
    Decidable (Partner code d e) := inferInstanceAs (Decidable (_ ∧ _))

theorem existsUnique_partner {n m : Nat} (code : Code n m) (h : Valid code)
    (d : Position n) : ∃! e, Partner code d e := by
  have hd : d.1 ∈ endpoints code (code d.1 d.2) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, d.2, rfl⟩
  have hcard : ((endpoints code (code d.1 d.2)).erase d.1).card = 1 := by
    rw [Finset.card_erase_of_mem hd, h.2]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hcard
  have hv' : v ∈ (endpoints code (code d.1 d.2)).erase d.1 := by simp [hv]
  obtain ⟨i, hi⟩ := (Finset.mem_filter.1 (Finset.mem_erase.1 hv').2).2
  refine ⟨(v, i), ⟨(Finset.mem_erase.1 hv').1.symm, hi⟩, ?_⟩
  intro e he
  have he' : e.1 ∈ (endpoints code (code d.1 d.2)).erase d.1 :=
    Finset.mem_erase.2 ⟨he.1.symm,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, e.2, he.2⟩⟩
  have hev : e.1 = v := by simpa [hv] using he'
  apply Prod.ext hev
  apply h.1 v
  simpa [hev] using he.2.trans hi.symm

def mate {n m : Nat} (code : Code n m) (h : Valid code) (d : Position n) :
    Position n :=
  Finset.univ.choose (Partner code d) (by
    simpa only [Finset.mem_univ, true_and] using existsUnique_partner code h d)

theorem mate_partner {n m : Nat} (code : Code n m) (h : Valid code)
    (d : Position n) : Partner code d (mate code h d) :=
  Finset.choose_property _ _ _

theorem partner_symm {n m : Nat} {code : Code n m} {d e : Position n}
    (h : Partner code d e) : Partner code e d := ⟨h.1.symm, h.2.symm⟩

theorem mate_involutive {n m : Nat} (code : Code n m) (h : Valid code) :
    Function.Involutive (mate code h) := by
  intro d
  exact (existsUnique_partner code h (mate code h d)).unique
    (mate_partner code h _) (partner_symm (mate_partner code h d))

def matePerm {n m : Nat} (code : Code n m) (h : Valid code) :
    Equiv.Perm (Position n) where
  toFun := mate code h
  invFun := mate code h
  left_inv := mate_involutive code h
  right_inv := mate_involutive code h

theorem matePerm_eq_alpha {n m : Nat} (code : RotationCode n m)
    (h : code.Valid) : matePerm code.incidence h.1 = code.alpha := by
  ext d : 1
  exact (existsUnique_partner code.incidence h.1 d).unique
    (mate_partner code.incidence h.1 d) ⟨h.2.2.2.2.1 d, h.2.2.2.1 d⟩

def signedRotation {n : Nat} (sign : Fin n → Bool) : Equiv.Perm (Position n) where
  toFun d := (d.1, if sign d.1 then d.2 + 1 else d.2 - 1)
  invFun d := (d.1, if sign d.1 then d.2 - 1 else d.2 + 1)
  left_inv := by intro d; rcases d with ⟨v, i⟩; cases h : sign v <;> simp [h]
  right_inv := by intro d; rcases d with ⟨v, i⟩; cases h : sign v <;> simp [h]

private theorem three_derangement (f : Fin 3 → Fin 3)
    (hi : Function.Injective f) (hf : ∀ i, f i ≠ i) :
    ∀ i, f i = if f 0 = 1 then i + 1 else i - 1 := by
  revert f hi hf
  decide +kernel

def orientation {n m : Nat} (code : RotationCode n m) (v : Fin n) : Bool :=
  decide ((code.rho (v, 0)).2 = 1)

theorem signedRotation_eq_rho {n m : Nat} (code : RotationCode n m)
    (h : code.Valid) : signedRotation (orientation code) = code.rho := by
  have hv := h.2.2.2.2.2.1
  have hc := h.2.2.2.2.2.2
  ext d : 1
  rcases d with ⟨v, i⟩
  have hinj : Function.Injective (fun j : Fin 3 => (code.rho (v, j)).2) := by
    intro a b hab
    exact congrArg Prod.snd (code.rho.injective
      (Prod.ext ((hv (v, a)).trans (hv (v, b)).symm) hab))
  have hfree : ∀ j : Fin 3, (code.rho (v, j)).2 ≠ j := by
    intro j hj
    have heq := (hc (v, j) (v, j + 1) rfl).eq_of_left (Prod.ext (hv _) hj)
    have bad := congrArg Prod.snd heq
    have : ∀ a : Fin 3, a ≠ a + 1 := by decide +kernel
    exact this j bad
  refine Prod.ext ?_ ?_
  · exact (hv (v, i)).symm
  · simpa [signedRotation, orientation] using (three_derangement _ hinj hfree i).symm

abbrev CompactCode (n m : Nat) := Code n m × (Fin n → Bool)

def CompactCode.decode {n m : Nat} (code : CompactCode n m) :
    Option (RotationCode n m) :=
  if h : Valid code.1 then some ⟨code.1, matePerm code.1 h, signedRotation code.2⟩
  else none

def RotationCode.compress {n m : Nat} (code : RotationCode n m) : CompactCode n m :=
  ⟨code.incidence, orientation code⟩

theorem decode_compress {n m : Nat} (code : RotationCode n m) (h : code.Valid) :
    code.compress.decode = some code := by
  simp only [CompactCode.decode, RotationCode.compress, dif_pos h.1]
  rw [matePerm_eq_alpha code h, signedRotation_eq_rho code h]
  rfl

abbrev BoundedCompactCode (bound : Nat) :=
  Σ n : Fin (bound + 1), Σ m : Fin (3 * bound / 2 + 1), CompactCode n.val m.val

def CompactCode.passes {n m : Nat} (code : CompactCode n m) : Bool :=
  match code.decode with
  | none => true
  | some decoded => !decoded.admissible || hasColouring decoded.incidence

def compactAudit (bound : Nat) : Bool :=
  decide (∀ code : BoundedCompactCode bound, code.2.2.passes = true)

theorem baseAudit_iff (bound : Nat) :
    baseAudit bound = true ↔ ∀ code : BoundedRotationCode bound,
      code.2.2.admissible = true → hasColouring code.2.2.incidence = true := by
  simp [baseAudit, badSphericalCodes, sphericalEnvelope, Finset.filter_eq_empty_iff]

/-- Compression changes the representation, not the finite-base question. -/
theorem compactAudit_iff_baseAudit (bound : Nat) :
    compactAudit bound = true ↔ baseAudit bound = true := by
  rw [baseAudit_iff]
  simp only [compactAudit, decide_eq_true_eq]
  constructor
  · intro ha code hc
    have hvalid : code.2.2.Valid := by
      have hfields := hc
      simp only [RotationCode.admissible, Bool.and_eq_true, decide_eq_true_eq] at hfields
      exact hfields.1.1.1
    have hp := ha ⟨code.1, code.2.1, code.2.2.compress⟩
    change code.2.2.compress.passes = true at hp
    rw [CompactCode.passes, decode_compress code.2.2 hvalid] at hp
    simpa [hc] using hp
  · intro ha ⟨n, m, code⟩
    change code.passes = true
    unfold CompactCode.passes
    cases hd : code.decode with
    | none => rfl
    | some decoded =>
      by_cases hc : decoded.admissible = true
      · simpa [hc] using ha ⟨n, m, decoded⟩ hc
      · simp [Bool.eq_false_of_not_eq_true hc]

theorem taitBaseVerifiedAt_of_compactAudit (bound : Nat)
    (ha : compactAudit bound = true) :
    GoertzelV24SphericalReductiveAssembly.TaitBaseVerifiedAt.{u} bound :=
  taitBaseVerifiedAt_of_baseAudit bound ((compactAudit_iff_baseAudit bound).1 ha)

theorem card_compactCode (n m : Nat) :
    Fintype.card (CompactCode n m) = m ^ (3 * n) * 2 ^ n := by
  simp [CompactCode, Code, ← pow_mul]

theorem card_boundedCompactCode (bound : Nat) :
    Fintype.card (BoundedCompactCode bound) =
      ∑ n : Fin (bound + 1), ∑ m : Fin (3 * bound / 2 + 1),
        (m : Nat) ^ (3 * (n : Nat)) * 2 ^ (n : Nat) := by
  simp only [BoundedCompactCode, Fintype.card_sigma, card_compactCode]

theorem compact_code_count_two : Fintype.card (BoundedCompactCode 2) = 3252 := by
  rw [card_boundedCompactCode]
  decide +kernel

/-! This audit has a nonempty multigraph-code domain (parallel triples).
The graph-backed simple cubic class at this bound is still empty. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem compactAudit_two : compactAudit 2 = true := by decide +kernel

/-- Transfer the successful tiny audit without enumerating the raw carrier. -/
theorem baseAudit_two : baseAudit 2 = true :=
  (compactAudit_iff_baseAudit 2).1 compactAudit_two

end Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
