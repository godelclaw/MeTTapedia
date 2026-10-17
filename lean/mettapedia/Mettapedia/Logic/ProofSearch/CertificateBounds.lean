import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.FinRange

/-!
# Finite certificate search and the obstruction to computable length bounds

Certificates are finite words over `Fin q`. Every length-bounded space is
enumerated explicitly, including the empty word and the zero-letter alphabet.
The search returns an actual certificate and is computable whenever the original
checker is computable. Consequently, sound checking with a computable positive
certificate bound decides the checked meaning. An undecidable meaning cannot
have such a bound, even when checking each supplied certificate terminates.

The encoding corollary uses the existing fail-closed `Checker.PartialCodec` and
`Checker.onWire`; it requires a computable decoder and charges the encoded word
length. Merely having a computably encodable abstract certificate type does not
make a bounded abstract size a finite, effectively searchable space.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.CertificateBounds

open Mettapedia.GSLT.LanguageDef.KernelAuthority

variable {Claim Certificate : Type} {q : Nat}

/-- Prepend each possible letter, retaining the empty word. -/
def extendWords (q : Nat) (previous : List (List (Fin q))) : List (List (Fin q)) :=
  [] :: (List.finRange q).flatMap (fun letter => previous.map (letter :: ·))

/-- Explicit finite enumeration of all certificate words of length at most `bound`. -/
def wordsUpTo (q : Nat) : Nat → List (List (Fin q)) :=
  Nat.rec [[]] (fun _ previous => extendWords q previous)

@[simp] theorem wordsUpTo_zero (q : Nat) : wordsUpTo q 0 = [[]] := rfl

@[simp] theorem wordsUpTo_succ (q bound : Nat) :
    wordsUpTo q (bound + 1) = extendWords q (wordsUpTo q bound) := rfl

/-- The enumeration is exact, rather than just containing some short certificates. -/
theorem mem_wordsUpTo (q bound : Nat) (word : List (Fin q)) :
    word ∈ wordsUpTo q bound ↔ word.length ≤ bound := by
  induction bound generalizing word with
  | zero => simp
  | succ bound ih =>
      cases word with
      | nil => simp [extendWords]
      | cons letter tail =>
          simp [extendWords, List.mem_flatMap, List.mem_map, ih]

theorem extendWords_primrec (q : Nat) : Primrec (extendWords q) := by
  have prepend : Primrec (fun input : List (List (Fin q)) × Fin q =>
      input.1.map (input.2 :: ·)) :=
    Primrec.list_map Primrec.fst
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp (Primrec.const [])
    (Primrec.list_flatMap (Primrec.const (List.finRange q)) prepend.to₂)

theorem wordsUpTo_primrec (q : Nat) : Primrec (wordsUpTo q) :=
  Primrec.nat_rec₁ [[]] ((extendWords_primrec q).comp Primrec.snd).to₂

/-- Scan the first `count` list entries, keeping the first accepted certificate. -/
def scan (checker : Checker Claim Certificate) (claim : Claim)
    (certificates : List Certificate) : Nat → Option Certificate :=
  Nat.rec none (fun index previous => previous <|>
    (certificates[index]?).bind (fun certificate =>
      if checker.check claim certificate then some certificate else none))

/-- Exhaust the supplied finite list. No search oracles occur in this function. -/
def finiteSearch (checker : Checker Claim Certificate) (claim : Claim)
    (certificates : List Certificate) : Option Certificate :=
  scan checker claim certificates certificates.length

theorem scan_eq_find? (checker : Checker Claim Certificate) (claim : Claim)
    (certificates : List Certificate) (count : Nat) :
    scan checker claim certificates count =
      (certificates.take count).find? (checker.check claim) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (scan checker claim certificates count <|>
        (certificates[count]?).bind (fun certificate =>
          if checker.check claim certificate then some certificate else none)) = _
      rw [ih, List.take_add_one, List.find?_append]
      cases lookup : certificates[count]? with
      | none => simp
      | some certificate =>
          cases accepted : checker.check claim certificate <;> simp [accepted]

theorem finiteSearch_eq_find? (checker : Checker Claim Certificate) (claim : Claim)
    (certificates : List Certificate) :
    finiteSearch checker claim certificates = certificates.find? (checker.check claim) := by
  simp [finiteSearch, scan_eq_find?]

theorem scan_computable [Primcodable Claim] [Primcodable Certificate]
    (checker : Checker Claim Certificate)
    (checkerComputable : Computable (fun input : Claim × Certificate =>
      checker.check input.1 input.2)) :
    Computable (fun input : (Claim × List Certificate) × Nat =>
      scan checker input.1.1 input.1.2 input.2) := by
  have trial : Computable (fun input : (Claim × List Certificate) × Nat =>
      (input.1.2[input.2]?).bind (fun certificate =>
        if checker.check input.1.1 certificate then some certificate else none)) := by
    apply Computable.option_bind
      (Computable.list_getElem?.comp (Computable.snd.comp Computable.fst) Computable.snd)
    have claimProjection : Computable
        (fun input : ((Claim × List Certificate) × Nat) × Certificate => input.1.1.1) :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have callback : Computable
        (fun input : ((Claim × List Certificate) × Nat) × Certificate =>
          if checker.check input.1.1.1 input.2 then some input.2 else none) := by
      apply (Computable.cond
        (checkerComputable.comp (claimProjection.pair Computable.snd))
        (Computable.option_some.comp Computable.snd) (Computable.const none)).of_eq
      intro input
      cases checker.check input.1.1.1 input.2 <;> rfl
    exact callback.to₂
  exact Computable.nat_rec Computable.snd (Computable.const none)
    (Primrec.option_orElse.to_comp.comp (Computable.snd.comp Computable.snd)
      (trial.comp ((Computable.fst.comp Computable.fst).pair
        (Computable.fst.comp Computable.snd)))).to₂

theorem finiteSearch_computable [Primcodable Claim] [Primcodable Certificate]
    (checker : Checker Claim Certificate)
    (checkerComputable : Computable (fun input : Claim × Certificate =>
      checker.check input.1 input.2)) :
    Computable (fun input : Claim × List Certificate =>
      finiteSearch checker input.1 input.2) :=
  (scan_computable checker checkerComputable).comp
    (Computable.id.pair (Computable.list_length.comp Computable.snd))

/-- Search the actual finite word space supplied by the length bound. -/
def boundedSearch (checker : Checker Claim (List (Fin q))) (claim : Claim)
    (bound : Nat) : Option (List (Fin q)) :=
  finiteSearch checker claim (wordsUpTo q bound)

theorem boundedSearch_computable [Primcodable Claim]
    (checker : Checker Claim (List (Fin q)))
    (checkerComputable : Computable (fun input : Claim × List (Fin q) =>
      checker.check input.1 input.2)) :
    Computable (fun input : Claim × Nat => boundedSearch checker input.1 input.2) :=
  (finiteSearch_computable checker checkerComputable).comp
    (Computable.fst.pair ((wordsUpTo_primrec q).to_comp.comp Computable.snd))

theorem boundedSearch_isSome_iff (checker : Checker Claim (List (Fin q)))
    (claim : Claim) (bound : Nat) :
    (boundedSearch checker claim bound).isSome = true ↔
      ∃ certificate, certificate.length ≤ bound ∧ checker.check claim certificate = true := by
  simp [boundedSearch, finiteSearch_eq_find?, mem_wordsUpTo]

theorem boundedSearch_eq_some_sound (checker : Checker Claim (List (Fin q)))
    (claim : Claim) (bound : Nat) {certificate : List (Fin q)}
    (found : boundedSearch checker claim bound = some certificate) :
    certificate.length ≤ bound ∧ checker.check claim certificate = true := by
  have foundInList : (wordsUpTo q bound).find? (checker.check claim) = some certificate := by
    simpa [boundedSearch, finiteSearch_eq_find?] using found
  exact ⟨(mem_wordsUpTo q bound certificate).mp (List.mem_of_find?_eq_some foundInList),
    List.find?_some foundInList⟩

/-- Exhaustive refusal concerns exactly this finite certificate space. It does
not assert that the claim has no longer accepted certificate. -/
theorem boundedSearch_eq_none_iff (checker : Checker Claim (List (Fin q)))
    (claim : Claim) (bound : Nat) :
    boundedSearch checker claim bound = none ↔
      ∀ certificate, certificate.length ≤ bound → checker.check claim certificate = false := by
  rw [← Option.not_isSome_iff_eq_none, boundedSearch_isSome_iff]
  simp only [not_exists, not_and, Bool.not_eq_true]

/-- A computable bound covering positives turns total sound checking into a decision. -/
theorem computableMeaning_of_bound [Primcodable Claim]
    (checker : Checker Claim (List (Fin q))) {Meaning : Claim → Prop}
    (checkerComputable : Computable (fun input : Claim × List (Fin q) =>
      checker.check input.1 input.2))
    (sound : checker.Sound Meaning) (bound : Claim → Nat)
    (boundComputable : Computable bound)
    (covers : ∀ claim, Meaning claim →
      ∃ certificate, certificate.length ≤ bound claim ∧ checker.check claim certificate = true) :
    ComputablePred Meaning := by
  let decideMeaning := fun claim => (boundedSearch checker claim (bound claim)).isSome
  have computable : Computable decideMeaning :=
    Primrec.option_isSome.to_comp.comp
      ((boundedSearch_computable checker checkerComputable).comp
        (Computable.id.pair boundComputable))
  have exactSearch : ∀ claim, Meaning claim ↔ decideMeaning claim = true := by
    intro claim
    rw [boundedSearch_isSome_iff]
    constructor
    · exact covers claim
    · rintro ⟨certificate, _, accepted⟩
      exact sound claim certificate accepted
  exact ComputablePred.computable_iff.mpr
    ⟨decideMeaning, computable, funext (fun claim => propext (exactSearch claim))⟩

/-- Undecidability prohibits every computable positive-certificate length bound. -/
theorem no_computable_positive_bound [Primcodable Claim]
    (checker : Checker Claim (List (Fin q))) {Meaning : Claim → Prop}
    (checkerComputable : Computable (fun input : Claim × List (Fin q) =>
      checker.check input.1 input.2)) (sound : checker.Sound Meaning)
    (undecidableMeaning : ¬ ComputablePred Meaning) :
    ¬ ∃ bound : Claim → Nat, Computable bound ∧
      ∀ claim, Meaning claim →
        ∃ certificate, certificate.length ≤ bound claim ∧ checker.check claim certificate = true := by
  rintro ⟨bound, computable, covers⟩
  exact undecidableMeaning
    (computableMeaning_of_bound checker checkerComputable sound bound computable covers)

/-- Every computable bound misses a true claim whose accepted certificates are
all longer. Exact authority ensures this is a certified positive, not a claim
for which the checker lacks certificates altogether. -/
theorem positive_requires_longer [Primcodable Claim]
    (checker : Checker Claim (List (Fin q))) {Meaning : Claim → Prop}
    (checkerComputable : Computable (fun input : Claim × List (Fin q) =>
      checker.check input.1 input.2)) (authority : checker.Authority Meaning)
    (undecidableMeaning : ¬ ComputablePred Meaning)
    (bound : Claim → Nat) (boundComputable : Computable bound) :
    ∃ claim, Meaning claim ∧ (∃ certificate, checker.check claim certificate = true) ∧
      ∀ certificate, checker.check claim certificate = true → bound claim < certificate.length := by
  classical
  by_contra noLongPositive
  apply no_computable_positive_bound checker checkerComputable authority.sound
    undecidableMeaning
  refine ⟨bound, boundComputable, ?_⟩
  intro claim meaningful
  by_contra noShort
  apply noLongPositive
  refine ⟨claim, meaningful, authority.complete claim meaningful, ?_⟩
  intro certificate accepted
  apply Nat.lt_of_not_ge
  intro short
  exact noShort ⟨certificate, short, accepted⟩

/-! ## Existing fail-closed certificate encodings -/

/-- Computability of the original wire checker follows from the original
checker and decoder, including the decoder's refusal branch. -/
theorem onWire_computable [Primcodable Claim] [Primcodable Certificate]
    (checker : Checker Claim Certificate)
    (codec : Checker.PartialCodec Certificate (List (Fin q)))
    (checkerComputable : Computable (fun input : Claim × Certificate =>
      checker.check input.1 input.2)) (decoderComputable : Computable codec.decode) :
    Computable (fun input : Claim × List (Fin q) =>
      (Checker.onWire checker codec).check input.1 input.2) := by
  have claimProjection : Computable
      (fun input : (Claim × List (Fin q)) × Certificate => input.1.1) :=
    Computable.fst.comp Computable.fst
  apply (Computable.option_casesOn (decoderComputable.comp Computable.snd)
    (Computable.const false)
    (checkerComputable.comp (claimProjection.pair Computable.snd)).to₂).of_eq
  intro input
  cases decoded : codec.decode input.2 <;> simp [Checker.onWire, decoded]

theorem no_computable_encoded_positive_bound [Primcodable Claim] [Primcodable Certificate]
    (checker : Checker Claim Certificate) {Meaning : Claim → Prop}
    (codec : Checker.PartialCodec Certificate (List (Fin q)))
    (checkerComputable : Computable (fun input : Claim × Certificate =>
      checker.check input.1 input.2)) (decoderComputable : Computable codec.decode)
    (sound : checker.Sound Meaning) (undecidableMeaning : ¬ ComputablePred Meaning) :
    ¬ ∃ bound : Claim → Nat, Computable bound ∧
      ∀ claim, Meaning claim → ∃ certificate,
        (codec.encode certificate).length ≤ bound claim ∧ checker.check claim certificate = true := by
  rintro ⟨bound, computable, covers⟩
  apply no_computable_positive_bound (Checker.onWire checker codec)
    (onWire_computable checker codec checkerComputable decoderComputable)
    (Checker.onWire_sound codec sound) undecidableMeaning
  refine ⟨bound, computable, ?_⟩
  intro claim meaningful
  obtain ⟨certificate, short, accepted⟩ := covers claim meaningful
  exact ⟨codec.encode certificate, short, by
    simpa [Checker.onWire, codec.decode_encode] using accepted⟩

/-! ## Concrete decidable and undecidable controls -/

namespace Controls

/-- A simple genuine checker whose accepted word length is exactly the claim. -/
def lengthChecker : Checker Nat (List (Fin 2)) where
  check claim certificate := decide (certificate.length = claim)

theorem lengthChecker_computable :
    Computable (fun input : Nat × List (Fin 2) => lengthChecker.check input.1 input.2) :=
  (Primrec.eq.decide.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst).to_comp

theorem positive_search : boundedSearch lengthChecker 2 2 = some [0, 0] := rfl

theorem insufficient_bound : boundedSearch lengthChecker 2 1 = none := rfl

theorem negative_certificate : lengthChecker.check 2 [0, 1, 0] = false := rfl

theorem empty_alphabet (bound : Nat) : wordsUpTo 0 bound = [[]] := by
  induction bound with
  | zero => rfl
  | succ bound ih => simp [extendWords]

/-- Unary words encode actual step budgets for the existing halting checker. -/
def budgetCodec : Checker.PartialCodec Nat (List (Fin 1)) where
  encode budget := List.replicate budget 0
  decode word := some word.length
  decode_encode budget := by simp

theorem budgetCodec_decoder_computable : Computable budgetCodec.decode :=
  Computable.option_some.comp Computable.list_length

/-- An explicit undecidable checker instance rules out even a computable bound
on its unary budget certificates. It still checks each supplied budget totally. -/
theorem halting_no_computable_certificate_bound :
    ¬ ∃ bound : Nat.Partrec.Code → Nat, Computable bound ∧
      ∀ code, Checker.HaltingMeaning code → ∃ budget,
        budget ≤ bound code ∧ Checker.haltingTrustBoundaryChecker.check code budget = true := by
  simpa [budgetCodec] using
    no_computable_encoded_positive_bound Checker.haltingTrustBoundaryChecker budgetCodec
      Checker.haltingTrustBoundaryChecker_computable budgetCodec_decoder_computable
      Checker.haltingTrustBoundaryChecker_sound Checker.haltingMeaning_not_computable

end Controls

end Mettapedia.Logic.ProofSearch.CertificateBounds
