import Mettapedia.GSLT.LanguageDef.GSLTILNativeKernel
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Native GSLT-ML command journals on a finite wire

This is a structural request format for the existing at/via command core,
not a parser for authored `.module` text. The finite-catalog profile retains
the entire catalog and every selected row ordinal. It proves derivability
relative to those submitted rows, not the truth of an external axiom catalog.
The Tick profile uses the fixed independently specified unbounded native fibre.

Complete canonical decoding rejects trailing words, unknown profiles and
alternate encodings. Neither profile selects another language as its meaning.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel.Wire

open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec

/-- Reuse the complete structural Pattern token codec, including binder,
collection and raw substitution metadata. These payloads are not evaluated. -/
private def patternCodec : Codec Pattern :=
  (Codec.list Codec.string).mapped PatternTokens.encode PatternTokens.decode
    PatternTokens.decode_encode

private def unitCodec : Codec Unit where
  put _ := .atom 0
  get | .atom 0 => some () | _ => none
  get_put _ := rfl

private def putCommand : Command → Data
  | .at stage state => .pair (.atom 0)
      ((Codec.prod patternCodec patternCodec).put (stage, state))
  | .via kind route sourceStage targetStage state => .pair (.atom 1)
      ((Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod patternCodec
        (Codec.prod patternCodec patternCodec)))).put
        (kind, route, sourceStage, targetStage, state))

private def getCommand : Data → Option Command
  | .pair (.atom 0) fields => do
      let (stage, state) ← (Codec.prod patternCodec patternCodec).get fields
      pure (.at stage state)
  | .pair (.atom 1) fields => do
      let (kind, route, sourceStage, targetStage, state) ←
        (Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod patternCodec
          (Codec.prod patternCodec patternCodec)))).get fields
      pure (.via kind route sourceStage targetStage state)
  | _ => none

def commandCodec : Codec Command := ⟨putCommand, getCommand, fun command => by
  cases command <;> simp only [putCommand, getCommand, Codec.get_put] <;> rfl⟩

private def putEntry {F T : Type} (fibre : Codec F) (transport : Codec T) :
    Entry F T → Data
  | .fibre next proof => .pair (.atom 0) ((Codec.prod patternCodec fibre).put (next, proof))
  | .underneath next proof => .pair (.atom 1) ((Codec.prod patternCodec fibre).put (next, proof))
  | .transport next proof => .pair (.atom 2) ((Codec.prod patternCodec transport).put (next, proof))

private def getEntry {F T : Type} (fibre : Codec F) (transport : Codec T) :
    Data → Option (Entry F T)
  | .pair (.atom 0) fields => do
      let (next, proof) ← (Codec.prod patternCodec fibre).get fields
      pure (.fibre next proof)
  | .pair (.atom 1) fields => do
      let (next, proof) ← (Codec.prod patternCodec fibre).get fields
      pure (.underneath next proof)
  | .pair (.atom 2) fields => do
      let (next, proof) ← (Codec.prod patternCodec transport).get fields
      pure (.transport next proof)
  | _ => none

def entryCodec {F T : Type} (fibre : Codec F) (transport : Codec T) : Codec (Entry F T) :=
  ⟨putEntry fibre transport, getEntry fibre transport, fun entry => by
    cases entry <;> simp only [putEntry, getEntry, Codec.get_put] <;> rfl⟩

def catalogJournalCodec : Codec (List (Entry Nat Nat)) := Codec.list (entryCodec Codec.nat Codec.nat)
def tickJournalCodec : Codec (Journal Tick.evidence) := Codec.list (entryCodec unitCodec unitCodec)

private def fibreRowCodec : Codec FibreRow :=
  (Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod patternCodec patternCodec))).mapped
    (fun row => (row.occurrence, row.stage, row.source, row.target))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩)
    (fun _ => rfl)

private def transportRowCodec : Codec TransportRow :=
  (Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod patternCodec
    (Codec.prod patternCodec (Codec.prod patternCodec (Codec.prod patternCodec patternCodec)))))).mapped
    (fun row => (row.occurrence, row.kind, row.route, row.sourceStage, row.targetStage,
      row.source, row.target))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2.1, fields.2.2.2.2.2.2⟩)
    (fun _ => rfl)

def catalogCodec : Codec Catalog :=
  (Codec.prod (Codec.list fibreRowCodec) (Codec.list transportRowCodec)).mapped
    (fun catalog => (catalog.fibreRows, catalog.transportRows))
    (fun fields => some ⟨fields.1, fields.2⟩) (fun _ => rfl)

/-- Source authority includes all catalog data, not just a hash or a name. -/
theorem catalog_header_exact (first last : Catalog) :
    catalogCodec.put first = catalogCodec.put last ↔ first = last :=
  catalogCodec.put_injective.eq_iff

inductive Packet where
  | catalog (rules : Catalog) (first last : Command) (journal : List (Entry Nat Nat))
  | tick (first last : Command) (journal : Journal Tick.evidence)

private def catalogFields := Codec.prod catalogCodec
  (Codec.prod commandCodec (Codec.prod commandCodec catalogJournalCodec))
private def tickFields := Codec.prod commandCodec (Codec.prod commandCodec tickJournalCodec)

private def putPacket : Packet → Data
  | .catalog rules first last journal =>
      .pair (.atom 0) (catalogFields.put (rules, first, last, journal))
  | .tick first last journal => .pair (.atom 1) (tickFields.put (first, last, journal))

private def getPacket : Data → Option Packet
  | .pair (.atom 0) fields => do
      let (rules, first, last, journal) ← catalogFields.get fields
      pure (.catalog rules first last journal)
  | .pair (.atom 1) fields => do
      let (first, last, journal) ← tickFields.get fields
      pure (.tick first last journal)
  | _ => none

private def payloadCodec : Codec Packet := ⟨putPacket, getPacket, fun packet => by
  cases packet <;> simp only [putPacket, getPacket, Codec.get_put] <;> rfl⟩

def packetTag : String := "GSLT.NativeCommand.v1"

def packetCodec : Codec Packet :=
  (Codec.prod Codec.string payloadCodec).mapped
    (fun packet => (packetTag, packet))
    (fun fields => if fields.1 = packetTag then some fields.2 else none)
    (fun _ => if_pos rfl)

/-- Independent per-journal authority retains each original row selection. -/
def Packet.Judges : Packet → Prop
  | .catalog rules first last journal => JournalJudges (catalogEvidence rules) journal first last
  | .tick first last journal => JournalJudges Tick.evidence journal first last

def Packet.check : Packet → Bool
  | .catalog rules first last journal => NativeKernel.check (catalogChecking rules) first last journal
  | .tick first last journal => NativeKernel.check Tick.checking first last journal

theorem Packet.check_exact (packet : Packet) : packet.check = true ↔ packet.Judges := by
  cases packet <;> exact NativeKernel.check_exact _ _ _ _

def encode (packet : Packet) : List Binary.Alphabet := Binary.encodeWith packetCodec packet

/-- The result echoes the whole accepted source packet, including its exact
journal and catalog. Refusal returns no authority claim. -/
def checkWord (word : List Binary.Alphabet) : Option Packet := do
  let packet ← Binary.canonicalDecodeWith packetCodec word
  if packet.check then some packet else none

theorem checkWord_exact (word : List Binary.Alphabet) (packet : Packet) :
    checkWord word = some packet ↔ encode packet = word ∧ packet.Judges := by
  constructor
  · intro accepted
    obtain ⟨decoded, decodedEq, checked⟩ := Option.bind_eq_some_iff.mp accepted
    split at checked
    · next yes =>
        have same : decoded = packet := Option.some.inj checked
        subst decoded
        exact ⟨(Binary.canonicalDecodeWith_exact _ _ _).mp decodedEq,
          (Packet.check_exact packet).mp yes⟩
    · cases checked
  · rintro ⟨rfl, valid⟩
    simp only [checkWord, encode, Binary.canonicalDecodeWith_encodeWith,
      Bind.bind, Option.bind, (Packet.check_exact packet).mpr valid, ite_true]

theorem catalog_source_iff_word (rules : Catalog) (first last : Command) :
    (wireGSLT rules).MultiStep first.toPattern last.toPattern ↔
      ∃ journal, checkWord (encode (.catalog rules first last journal)) =
        some (.catalog rules first last journal) := by
  rw [← catalog_accepted_iff_wire_paths]
  constructor
  · rintro ⟨journal, accepted⟩
    exact ⟨journal, (checkWord_exact _ _).mpr
      ⟨rfl, (check_exact _ _ _ _).mp accepted⟩⟩
  · rintro ⟨journal, accepted⟩
    exact ⟨journal, (check_exact _ _ _ _).mpr ((checkWord_exact _ _).mp accepted).2⟩

theorem tick_source_iff_word (first last : Command) :
    Runs Tick.source first last ↔
      ∃ journal, checkWord (encode (.tick first last journal)) = some (.tick first last journal) := by
  rw [← accepted_iff_runs Tick.coverage Tick.checking]
  constructor
  · rintro ⟨journal, accepted⟩
    exact ⟨journal, (checkWord_exact _ _).mpr ⟨rfl, (check_exact _ _ _ _).mp accepted⟩⟩
  · rintro ⟨journal, accepted⟩
    exact ⟨journal, (check_exact _ _ _ _).mpr ((checkWord_exact _ _).mp accepted).2⟩

/-- Optional installed-catalog checking requires equality of the complete
source header, not an unverified catalog identifier. -/
def checkAgainst (rules : Catalog) (word : List Binary.Alphabet) : Option Packet := do
  let packet ← checkWord word
  match packet with
  | .catalog submitted _ _ _ =>
      if catalogCodec.put submitted = catalogCodec.put rules then some packet else none
  | .tick .. => none

theorem checkAgainst_source (rules : Catalog) (word : List Binary.Alphabet) (packet : Packet)
    (accepted : checkAgainst rules word = some packet) :
    ∃ first last journal, packet = .catalog rules first last journal ∧
      encode packet = word ∧ packet.Judges := by
  obtain ⟨decoded, decodedEq, checked⟩ := Option.bind_eq_some_iff.mp accepted
  cases decoded with
  | tick first last journal =>
      change none = some packet at checked
      cases checked
  | catalog submitted first last journal =>
      change (if catalogCodec.put submitted = catalogCodec.put rules then
        some (.catalog submitted first last journal) else none) = some packet at checked
      split at checked
      · next same =>
          have catalogEq := catalogCodec.put_injective same
          subst submitted
          have packetEq : Packet.catalog rules first last journal = packet := Option.some.inj checked
          subst packet
          exact ⟨first, last, journal, rfl, (checkWord_exact _ _).mp decodedEq⟩
      · cases checked

#print axioms checkWord_exact
#print axioms catalog_source_iff_word
#print axioms tick_source_iff_word
#print axioms checkAgainst_source

end Mettapedia.GSLT.LanguageDef.GSLTIL.NativeKernel.Wire
