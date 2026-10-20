import Mettapedia.GSLT.LanguageDef.MacroExportStateful

/-!
# Counter tables: the dense profile, checked on the actual rows

`cesta export-header` writes a counter table, `(cesta-counters/1 ... (rows (ID
NAME "spelling") ...))`, as a C enumeration with its count and a spelling
array. `Dense` states what the dense profile promises the C it generates
relies on: identifiers 0 to n-1 in order, distinct names and spellings, names
that are C identifiers under the prefix, printable spellings without quotes or
backslashes, and a count name no row takes. `checkDense` decides it for a
table at once. For a large table, `dense_of_checked` assembles it from checks
the kernel runs in pieces: `rowsOk` reads each name and spelling once, giving its
number under an injective encoding and its character checks, over a chunk of
rows at a time; distinctness is then decided on the numbers alone, through a
search tree.
-/

namespace Mettapedia.GSLT.LanguageDef.ExportCounterTables

open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)
open Mettapedia.GSLT.LanguageDef.MacroExportStateful (digits)

set_option autoImplicit false

structure Row where
  id : Nat
  name : String
  spelling : String

structure Table where
  enum : String
  namePrefix : String
  count : String
  names : String
  rows : List Row

def decodeRow : Atom → Option Row
  | .list [.symbol id, .symbol name, .text spelling] => do
      let n ← digits id.toList
      pure ⟨n, name, spelling⟩
  | _ => none

def decodeTable : Atom → Option Table
  | .list [.symbol "cesta-counters/1", .list [.symbol "enum", .symbol enum], .list [.symbol "prefix", .symbol p],
      .list [.symbol "count", .symbol count], .list [.symbol "names", .symbol names],
      .list [.symbol "profile", .symbol "dense"], .list (.symbol "rows" :: rows)] => do
      let rows ← rows.mapM decodeRow
      pure ⟨enum, p, count, names, rows⟩
  | _ => none

/-! ## The dense profile -/

def identifierStart (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'

def identifierChar (c : Char) : Bool := identifierStart c || ('0' ≤ c && c ≤ '9')

def cIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => identifierStart c && cs.all identifierChar

/-- Printable ASCII payload without quotes or backslashes. A payload may
contain question marks; the C emitter escapes those to prevent trigraph
replacement, without changing the decoded spelling. -/
def printableSpelling (s : String) : Bool :=
  s.toList.all fun c => decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\'

/-- What the C a dense table generates relies on. -/
structure Dense (t : Table) : Prop where
  ids : ∀ k (h : k < t.rows.length), t.rows[k].id = k
  names : (t.count :: t.rows.map Row.name).Nodup
  spellings : (t.rows.map Row.spelling).Nodup
  identifiers : ∀ r ∈ t.rows, cIdentifier (t.namePrefix ++ r.name) = true
  countIdentifier : cIdentifier (t.namePrefix ++ t.count) = true
  printable : ∀ r ∈ t.rows, printableSpelling r.spelling = true

/-! ## Distinct strings as distinct numbers -/

/-- Base-256 digits of the characters, each shifted up by one so no digit is 0. -/
def encodeChars : List Char → Nat
  | [] => 0
  | c :: rest => encodeChars rest * 256 + (c.toNat + 1)

def encode (s : String) : Nat := encodeChars s.toList

def narrow (s : String) : Bool := s.toList.all fun c => decide (c.toNat < 255)

theorem encodeChars_injective : ∀ {a b : List Char}, (∀ c ∈ a, c.toNat < 255) → (∀ c ∈ b, c.toNat < 255) →
    encodeChars a = encodeChars b → a = b
  | [], [], _, _, _ => rfl
  | [], d :: s, _, _, h => by simp [encodeChars] at h
  | c :: r, [], _, _, h => by simp [encodeChars] at h
  | c :: r, d :: s, ha, hb, h => by
      simp only [encodeChars] at h
      have hc := ha c (by simp)
      have hd := hb d (by simp)
      have hdigit : c.toNat + 1 = d.toNat + 1 := by omega
      have hrest : encodeChars r = encodeChars s := by omega
      have hcd : c = d := Char.toNat_inj.mp (by omega)
      subst hcd
      rw [encodeChars_injective (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])) hrest]

theorem encode_injective {a b : String} (ha : narrow a = true) (hb : narrow b = true) (h : encode a = encode b) :
    a = b := by
  unfold narrow at ha hb
  simp only [List.all_eq_true, decide_eq_true_eq] at ha hb
  exact String.toList_inj.mp (encodeChars_injective ha hb h)

/-! ## Distinct numbers through a search tree -/

inductive Keys where
  | leaf
  | node (left : Keys) (key : Nat) (right : Keys)

def Keys.mem (x : Nat) : Keys → Prop
  | .leaf => False
  | .node l k r => l.mem x ∨ x = k ∨ r.mem x

/-- Every key strictly between the bounds. -/
def Keys.Within (lo hi : Option Nat) : Keys → Prop
  | .leaf => True
  | .node l k r => (∀ a, lo = some a → a < k) ∧ (∀ b, hi = some b → k < b) ∧ l.Within lo (some k) ∧
      r.Within (some k) hi

/-- Insert a new key; `none` when it is already present. -/
def Keys.insert (x : Nat) : Keys → Option Keys
  | .leaf => some (.node .leaf x .leaf)
  | .node l k r =>
      if x < k then (l.insert x).map fun l' => .node l' k r
      else if k < x then (r.insert x).map fun r' => .node l k r'
      else none

def allDistinct : List Nat → Keys → Bool
  | [], _ => true
  | x :: rest, t => match t.insert x with
    | some t' => allDistinct rest t'
    | none => false

theorem Keys.mem_bounds {lo hi : Option Nat} : ∀ {t : Keys}, t.Within lo hi → ∀ {x : Nat}, t.mem x →
    (∀ a, lo = some a → a < x) ∧ (∀ b, hi = some b → x < b)
  | .leaf, _, _, h => h.elim
  | .node l k r, ⟨hlo, hhi, hl, hr⟩, x, h => by
      rcases h with h | rfl | h
      · obtain ⟨h1, h2⟩ := Keys.mem_bounds hl h
        exact ⟨h1, fun b hb => Nat.lt_trans (h2 k rfl) (hhi b hb)⟩
      · exact ⟨hlo, hhi⟩
      · obtain ⟨h1, h2⟩ := Keys.mem_bounds hr h
        exact ⟨fun a ha => Nat.lt_trans (hlo a ha) (h1 k rfl), h2⟩

/-- Inserting into an ordered tree: a fresh key gives an ordered tree with it
added, and refusal means the key is present. -/
theorem Keys.insert_spec : ∀ {t : Keys} {lo hi : Option Nat} {x : Nat}, t.Within lo hi →
    (∀ a, lo = some a → a < x) → (∀ b, hi = some b → x < b) →
    match t.insert x with
    | some t' => t'.Within lo hi ∧ (∀ y, t'.mem y ↔ y = x ∨ t.mem y) ∧ ¬ t.mem x
    | none => t.mem x
  | .leaf, lo, hi, x, _, hlo, hhi => by
      simp only [Keys.insert]
      exact ⟨⟨hlo, hhi, trivial, trivial⟩, fun y => by simp [Keys.mem], fun h => h⟩
  | .node l k r, lo, hi, x, ⟨hk1, hk2, hl, hr⟩, hlo, hhi => by
      simp only [Keys.insert]
      by_cases h1 : x < k
      · rw [if_pos h1]
        have ih := Keys.insert_spec (x := x) hl hlo (fun b hb => by cases hb; exact h1)
        cases hi' : l.insert x with
        | none => rw [hi'] at ih; exact Or.inl ih
        | some l' =>
            rw [hi'] at ih
            obtain ⟨hw, hm, hn⟩ := ih
            refine ⟨⟨hk1, hk2, hw, hr⟩, fun y => ?_, ?_⟩
            · simp only [Keys.mem, hm y]; tauto
            · rintro (h | h | h)
              · exact hn h
              · omega
              · have := (Keys.mem_bounds hr h).1 k rfl; omega
      · rw [if_neg h1]
        by_cases h2 : k < x
        · rw [if_pos h2]
          have ih := Keys.insert_spec (x := x) hr (fun a ha => by cases ha; exact h2) hhi
          cases hi' : r.insert x with
          | none => rw [hi'] at ih; exact Or.inr (Or.inr ih)
          | some r' =>
              rw [hi'] at ih
              obtain ⟨hw, hm, hn⟩ := ih
              refine ⟨⟨hk1, hk2, hl, hw⟩, fun y => ?_, ?_⟩
              · simp only [Keys.mem, hm y]; tauto
              · rintro (h | h | h)
                · have := (Keys.mem_bounds hl h).2 k rfl; omega
                · omega
                · exact hn h
        · rw [if_neg h2]
          exact Or.inr (Or.inl (by omega))

theorem allDistinct_sound : ∀ {xs : List Nat} {t : Keys}, t.Within none none → allDistinct xs t = true →
    xs.Nodup ∧ ∀ x ∈ xs, ¬ t.mem x
  | [], _, _, _ => ⟨.nil, fun _ h => by cases h⟩
  | x :: rest, t, hw, h => by
      have spec := Keys.insert_spec (x := x) hw (fun _ h => by cases h) (fun _ h => by cases h)
      simp only [allDistinct] at h
      cases hi : t.insert x with
      | none => rw [hi] at h; cases h
      | some t' =>
          rw [hi] at h spec
          obtain ⟨hw', hm, hn⟩ := spec
          obtain ⟨hnd, hfresh⟩ := allDistinct_sound hw' h
          refine ⟨List.nodup_cons.mpr ⟨fun hx => hfresh x hx ((hm x).mpr (.inl rfl)), hnd⟩, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hn
          · exact fun ht => hfresh y hy ((hm y).mpr (.inr ht))

theorem nodup_of_encoded {ss : List String} (hn : ∀ s ∈ ss, narrow s = true)
    (h : (ss.map encode).Nodup) : ss.Nodup := by
  induction ss with
  | nil => exact .nil
  | cons s rest ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
      refine List.nodup_cons.mpr ⟨fun hs => h.1 ⟨s, hs, rfl⟩, ih (fun x hx => hn x (by simp [hx])) h.2⟩

/-! ## The decision -/

def idsFrom : Nat → List Row → Bool
  | _, [] => true
  | k, r :: rest => r.id == k && idsFrom (k + 1) rest

def checkDense (t : Table) : Bool :=
  idsFrom 0 t.rows &&
    (t.count :: t.rows.map Row.name).all narrow && allDistinct ((t.count :: t.rows.map Row.name).map encode) .leaf &&
    (t.rows.map Row.spelling).all narrow && allDistinct ((t.rows.map Row.spelling).map encode) .leaf &&
    t.rows.all (fun r => cIdentifier (t.namePrefix ++ r.name)) && cIdentifier (t.namePrefix ++ t.count) &&
    t.rows.all (fun r => printableSpelling r.spelling)

theorem idsFrom_sound : ∀ {k : Nat} {rows : List Row}, idsFrom k rows = true →
    ∀ j (h : j < rows.length), rows[j].id = k + j
  | _, [], _, j, h => by simp at h
  | k, r :: rest, h, j, hj => by
      simp only [idsFrom, Bool.and_eq_true, beq_iff_eq] at h
      cases j with
      | zero => simpa using h.1
      | succ j =>
          have := idsFrom_sound h.2 j (by simpa using hj)
          simp only [List.getElem_cons_succ, this]; omega

theorem checkDense_sound {t : Table} (h : checkDense t = true) : Dense t := by
  simp only [checkDense, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hids, hnarrow⟩, hdistinct⟩, snarrow⟩, sdistinct⟩, hident⟩, hcount⟩, hprint⟩ := h
  refine ⟨fun k hk => by simpa using idsFrom_sound hids k hk, ?_, ?_, hident, hcount, hprint⟩
  · exact nodup_of_encoded hnarrow (allDistinct_sound (t := .leaf) trivial hdistinct).1
  · exact nodup_of_encoded snarrow (allDistinct_sound (t := .leaf) trivial sdistinct).1

/-- A counter table as written, checked. -/
def checkTable (a : Atom) : Bool :=
  match decodeTable a with
  | some t => checkDense t
  | none => false

/-- A table the kernel admits decodes, and has the dense profile. -/
theorem checkTable_sound {a : Atom} (h : checkTable a = true) : ∃ t, decodeTable a = some t ∧ Dense t := by
  unfold checkTable at h
  cases hd : decodeTable a with
  | none => rw [hd] at h; cases h
  | some t => rw [hd] at h; exact ⟨t, rfl, checkDense_sound h⟩

/-! ## Large tables, checked in pieces -/

/-- One pass over a name: its number, and whether it is narrow and made of
identifier characters. -/
def scanName : List Char → Nat × Bool
  | [] => (0, true)
  | c :: rest => match scanName rest with
    | (n, ok) => (n * 256 + (c.toNat + 1), ok && decide (c.toNat < 255) && identifierChar c)

/-- One pass over a spelling: its number, and whether it is narrow and printable. -/
def scanSpelling : List Char → Nat × Bool
  | [] => (0, true)
  | c :: rest => match scanSpelling rest with
    | (n, ok) => (n * 256 + (c.toNat + 1), ok && decide (c.toNat < 255) &&
        (decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\'))

theorem scanName_eq : ∀ cs : List Char,
    scanName cs = (encodeChars cs, cs.all fun c => decide (c.toNat < 255) && identifierChar c)
  | [] => rfl
  | c :: rest => by
      simp only [scanName, scanName_eq rest, encodeChars, List.all_cons]
      cases rest.all (fun c => decide (c.toNat < 255) && identifierChar c) <;>
        cases decide (c.toNat < 255) <;> cases identifierChar c <;> rfl

theorem scanSpelling_eq : ∀ cs : List Char,
    scanSpelling cs = (encodeChars cs, cs.all fun c => decide (c.toNat < 255) &&
      (decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\'))
  | [] => rfl
  | c :: rest => by
      simp only [scanSpelling, scanSpelling_eq rest, encodeChars, List.all_cons]
      generalize rest.all _ = x
      generalize (decide (32 ≤ c.toNat) && decide (c.toNat ≤ 126) && c != '"' && c != '\\') = y
      cases x <;> cases decide (c.toNat < 255) <;> cases y <;> rfl

/-- The rows' numbers are `names` and `spellings`, and each row's characters
pass. -/
def rowsOk : List Row → List Nat → List Nat → Bool
  | [], [], [] => true
  | r :: rows, n :: names, s :: spellings =>
      (match scanName r.name.toList with
       | (code, ok) => code == n && ok) &&
      (match scanSpelling r.spelling.toList with
       | (code, ok) => code == s && ok) &&
      rowsOk rows names spellings
  | _, _, _ => false

theorem rowsOk_append : ∀ {r1 r2 : List Row} {n1 n2 s1 s2 : List Nat},
    rowsOk r1 n1 s1 = true → rowsOk r2 n2 s2 = true → rowsOk (r1 ++ r2) (n1 ++ n2) (s1 ++ s2) = true
  | [], _, [], _, [], _, _, h2 => h2
  | [], _, _ :: _, _, _, _, h1, _ => by simp [rowsOk] at h1
  | [], _, [], _, _ :: _, _, h1, _ => by simp [rowsOk] at h1
  | _ :: _, _, [], _, _, _, h1, _ => by cases h1
  | _ :: _, _, _ :: _, _, [], _, h1, _ => by cases h1
  | r :: r1, r2, n :: n1, n2, s :: s1, s2, h1, h2 => by
      simp only [rowsOk, List.cons_append, Bool.and_eq_true] at h1 ⊢
      exact ⟨h1.1, rowsOk_append h1.2 h2⟩

theorem rowsOk_sound : ∀ {rows : List Row} {names spellings : List Nat}, rowsOk rows names spellings = true →
    rows.map (fun r => encode r.name) = names ∧ rows.map (fun r => encode r.spelling) = spellings ∧
      ∀ r ∈ rows, narrow r.name = true ∧ r.name.toList.all identifierChar = true ∧ narrow r.spelling = true ∧
        printableSpelling r.spelling = true
  | [], [], [], _ => ⟨rfl, rfl, fun _ h => by cases h⟩
  | [], _ :: _, _, h => by simp [rowsOk] at h
  | [], [], _ :: _, h => by simp [rowsOk] at h
  | _ :: _, [], _, h => by cases h
  | _ :: _, _ :: _, [], h => by cases h
  | r :: rows, n :: names, s :: spellings, h => by
      simp only [rowsOk, scanName_eq, scanSpelling_eq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hn, hnok⟩, hs, hsok⟩, hrest⟩ := h
      obtain ⟨h1, h2, h3⟩ := rowsOk_sound hrest
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hnok hsok
      refine ⟨by rw [List.map_cons, h1, ← hn]; rfl, by rw [List.map_cons, h2, ← hs]; rfl, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [narrow, List.all_eq_true, decide_eq_true_eq]; exact fun c hc => (hnok c hc).1
        · simp only [List.all_eq_true]; exact fun c hc => (hnok c hc).2
        · simp only [narrow, List.all_eq_true, decide_eq_true_eq]; exact fun c hc => (hsok c hc).1
        · simp only [printableSpelling, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          exact fun c hc => (hsok c hc).2
      · exact h3 x hx

theorem cIdentifier_append {p n : String} (hp : cIdentifier p = true) (hn : n.toList.all identifierChar = true) :
    cIdentifier (p ++ n) = true := by
  unfold cIdentifier at hp ⊢
  rw [String.toList_append]
  cases hq : p.toList with
  | nil => rw [hq] at hp; cases hp
  | cons c cs =>
      rw [hq] at hp
      simp only [List.cons_append, Bool.and_eq_true, List.all_append] at hp ⊢
      exact ⟨hp.1, hp.2, hn⟩

/-- The checks on a whole table that do not read every row's characters. -/
def tableOk (t : Table) (countCode : Nat) : Bool :=
  idsFrom 0 t.rows && cIdentifier t.namePrefix &&
    (match scanName t.count.toList with
     | (code, ok) => code == countCode && ok)

/-- A table whose rows pass `rowsOk`, whose numbers are distinct and whose
remaining checks pass has the dense profile. -/
theorem dense_of_checked (t : Table) (names spellings : List Nat) (countCode : Nat)
    (hrows : rowsOk t.rows names spellings = true) (hnames : allDistinct (countCode :: names) .leaf = true)
    (hspellings : allDistinct spellings .leaf = true) (htable : tableOk t countCode = true) : Dense t := by
  obtain ⟨hn, hs, hall⟩ := rowsOk_sound hrows
  simp only [tableOk, scanName_eq, Bool.and_eq_true, beq_iff_eq] at htable
  obtain ⟨⟨hids, hprefix⟩, hcode, hcount⟩ := htable
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcount
  have hcountNarrow : narrow t.count = true := by
    simp only [narrow, List.all_eq_true, decide_eq_true_eq]; exact fun c hc => (hcount c hc).1
  refine ⟨fun k hk => by simpa using idsFrom_sound hids k hk, ?_, ?_, fun r hr => ?_, ?_, fun r hr => (hall r hr).2.2.2⟩
  · have hd := (allDistinct_sound (t := .leaf) trivial hnames).1
    rw [← hn, ← hcode] at hd
    refine nodup_of_encoded (fun s hs' => ?_) (by simpa [encode, List.map_map, Function.comp_def] using hd)
    rcases List.mem_cons.mp hs' with rfl | hs'
    · exact hcountNarrow
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs'; exact (hall r hr).1
  · have hd := (allDistinct_sound (t := .leaf) trivial hspellings).1
    rw [← hs] at hd
    refine nodup_of_encoded (fun s hs' => ?_) (by simpa [encode, List.map_map, Function.comp_def] using hd)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs'; exact (hall r hr).2.2.1
  · exact cIdentifier_append hprefix (hall r hr).2.1
  · exact cIdentifier_append hprefix (by simp only [List.all_eq_true]; exact fun c hc => (hcount c hc).2)

/-! ## Examples -/

private def sample : Table :=
  ⟨"Probe", "PROBE_", "COUNT", "PROBE_NAMES", [⟨0, "A", "a"⟩, ⟨1, "B", "b"⟩]⟩

example : checkDense sample = true := by decide

/-- A trigraph-looking payload is valid data; its C representation must escape it. -/
example : checkDense { sample with rows := [⟨0, "A", "??="⟩] } = true := by decide

/-- A gap in the identifiers is refused. -/
example : checkDense { sample with rows := [⟨0, "A", "a"⟩, ⟨2, "B", "b"⟩] } = false := by decide

/-- A repeated name is refused, and so is a row named like the count. -/
example : checkDense { sample with rows := [⟨0, "A", "a"⟩, ⟨1, "A", "b"⟩] } = false := by decide
example : checkDense { sample with rows := [⟨0, "COUNT", "a"⟩] } = false := by decide

/-- A spelling a C string would have to escape is refused. -/
example : checkDense { sample with rows := [⟨0, "A", "a\"b"⟩] } = false := by decide

end Mettapedia.GSLT.LanguageDef.ExportCounterTables
