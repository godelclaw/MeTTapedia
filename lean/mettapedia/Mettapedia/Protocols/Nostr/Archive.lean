import Mettapedia.Protocols.Nostr.Mailbox

/-!
# The archived message as text

`Mailbox.lean` files a kept message as a structured `Mail.Message`. The client
stores it as text: one line `Name: value` per header, a blank line, then the
body. Its reader takes the first line that begins `Name:` and returns the rest
without leading blanks (`sed -n "/^Name:/{s/^Name:[[:space:]]*//;p;q}"`). The
watcher reads the sender, as the first word of `From:`, and the type, from
`X-Mailbox-Type:`, and runs control mail (`reset`, `limits`, `status`) by them.

The theorems:
- `hdrAll_reads_body`: the reader as first written searched the whole file, so
  a message without a type whose body quotes `X-Mailbox-Type: reset` read as a
  reset.
- `hdrBlock_file`: the corrected reader stops at the blank line. On a file whose
  header names and values hold no line break, it returns the first header of
  that name, whatever the body says.
- `hdrBlock_line_break`: a value must hold no line break, or it forges a header
  even for the corrected reader. `oneLine`, the client's `head -1 | tr -d '\r'`,
  removes them (`newline_not_mem_oneLine`).
- `watcherType_archive`, `watcherFrom_archive`: on the file the client writes,
  the type the watcher reads is the sealed letter's, and the sender it reads is
  the archived originator.
- `watcher_control_sound`: control mail the watcher reads as from the parent was
  composed by the parent, and carries a type the parent sealed.
- `renderTrustingTag_forges`, `render_originator_ignores_tags`: the `From:` name
  as first rendered was the event's `from_name` tag, which its author sets; the
  name the client renders now is a function of the signing key alone.

Text is modelled as characters (`List Char`). Header names are constants; the
watcher's control dispatch beyond the sender and the type is not modelled.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Nostr.Archive

open Mettapedia.Protocols.Nostr

/-- Text as characters: a line, a header name, a header value, a file. -/
abbrev Text := List Char

/-- The line `Name: value`. -/
def headerLine (name value : Text) : Text := name ++ ':' :: ' ' :: value

/-- The archive file: each header on its own line, a blank line, then the body. -/
def file (headers : List (Text × Text)) (body : Text) : Text :=
  (headers.map fun h => headerLine h.1 h.2 ++ ['\n']).flatten ++ '\n' :: body

/-- The reader's lines: the file split at line feeds. -/
def lines (t : Text) : List Text := t.splitOn '\n'

/-- What `s/^Name:[[:space:]]*//` leaves of a line that begins `Name:`. -/
def valueOf (name : Text) (l : Text) : Option Text :=
  if (name ++ [':']).isPrefixOf l then
    some ((l.drop (name.length + 1)).dropWhile Char.isWhitespace)
  else none

/-- The reader as first written: the first line of the whole file that begins
`Name:`. -/
def hdrAll (name : Text) (t : Text) : Option Text := (lines t).findSome? (valueOf name)

/-- The corrected reader: the first such line before the blank line that ends the
headers. -/
def hdrBlock (name : Text) (t : Text) : Option Text :=
  ((lines t).takeWhile fun l => !l.isEmpty).findSome? (valueOf name)

/-- A header name the reader can find: no colon and no line break. -/
def NameOk (name : Text) : Prop := ':' ∉ name ∧ '\n' ∉ name

/-- Headers the reader can find: every name is one, and no value breaks a line. -/
def HeadersOk (hs : List (Text × Text)) : Prop := ∀ h ∈ hs, NameOk h.1 ∧ '\n' ∉ h.2

/-! ## Names -/

/-- `From`. -/
def nameFrom : Text := ['F', 'r', 'o', 'm']
/-- `Subject`. -/
def nameSubject : Text := ['S', 'u', 'b', 'j', 'e', 'c', 't']
/-- `X-Mailbox-Type`. -/
def nameType : Text := ['X', '-', 'M', 'a', 'i', 'l', 'b', 'o', 'x', '-', 'T', 'y', 'p', 'e']
/-- `reset`, a control type. -/
def wordReset : Text := ['r', 'e', 's', 'e', 't']

theorem nameFrom_ok : NameOk nameFrom := ⟨by decide, by decide⟩
theorem nameSubject_ok : NameOk nameSubject := ⟨by decide, by decide⟩
theorem nameType_ok : NameOk nameType := ⟨by decide, by decide⟩

/-! ## The reader as first written reads the body -/

/-- A message from `lead` with no type, whose body quotes `X-Mailbox-Type: reset`:
the reader as first written takes the quotation for the message's type. -/
theorem hdrAll_reads_body :
    hdrAll nameType
      (file [(nameFrom, ['l', 'e', 'a', 'd']), (nameSubject, ['n', 'o', 't', 'e', 's'])]
        (nameType ++ ':' :: ' ' :: wordReset)) = some wordReset := by
  decide

/-- The corrected reader finds no type in the same file. -/
theorem hdrBlock_ignores_quotation :
    hdrBlock nameType
      (file [(nameFrom, ['l', 'e', 'a', 'd']), (nameSubject, ['n', 'o', 't', 'e', 's'])]
        (nameType ++ ':' :: ' ' :: wordReset)) = none := by
  decide

/-- A line break in a value starts a line of its own: a subject that carries
`\nX-Mailbox-Type: reset` forges the type even for the corrected reader. -/
theorem hdrBlock_line_break :
    hdrBlock nameType
      (file [(nameFrom, ['l', 'e', 'a', 'd']),
             (nameSubject, ['h', 'i'] ++ '\n' :: nameType ++ ':' :: ' ' :: wordReset)] []) =
      some wordReset := by
  decide

/-! ## The corrected reader on a well-formed file -/

theorem headerLine_ne_nil (name value : Text) : headerLine name value ≠ [] := by
  simp [headerLine]

theorem newline_not_mem_headerLine {name value : Text} (hn : '\n' ∉ name) (hv : '\n' ∉ value) :
    '\n' ∉ headerLine name value := by
  simp [headerLine, hn, hv]

/-- A file reads back as its header lines, a blank line, and the body's lines. -/
theorem lines_file {hs : List (Text × Text)} (h : HeadersOk hs) (body : Text) :
    lines (file hs body) = hs.map (fun h => headerLine h.1 h.2) ++ [] :: body.splitOn '\n' := by
  induction hs with
  | nil =>
    simpa [lines, file] using List.splitOn_append_cons_self_of_not_mem (a := '\n')
      (xs := ([] : Text)) (by simp) body
  | cons hd tl ih =>
    have hhd := h hd (by simp)
    have htl : HeadersOk tl := fun x hx => h x (by simp [hx])
    have hnl : '\n' ∉ headerLine hd.1 hd.2 := newline_not_mem_headerLine hhd.1.2 hhd.2
    have hfile : file (hd :: tl) body = headerLine hd.1 hd.2 ++ '\n' :: file tl body := by
      simp [file, List.append_assoc]
    rw [lines, hfile, List.splitOn_append_cons_self_of_not_mem hnl, ← lines, ih htl]
    simp

/-- The lines before the first blank one are exactly the header lines. -/
theorem takeWhile_header_lines (hs : List (Text × Text)) (rest : List Text) :
    ((hs.map (fun h => headerLine h.1 h.2)) ++ [] :: rest).takeWhile (fun l => !l.isEmpty) =
      hs.map (fun h => headerLine h.1 h.2) := by
  induction hs with
  | nil => simp
  | cons hd tl ih =>
    have hne : (headerLine hd.1 hd.2).isEmpty = false := by
      simp [headerLine_ne_nil]
    simp [hne, ih]

theorem isPrefixOf_headerLine_self (name value : Text) :
    (name ++ [':']).isPrefixOf (headerLine name value) = true := by
  simp [headerLine]

theorem isPrefixOf_headerLine_other {name name' : Text} (hn : ':' ∉ name) (hn' : ':' ∉ name')
    (hne : name ≠ name') (value : Text) :
    (name ++ [':']).isPrefixOf (headerLine name' value) = false := by
  induction name generalizing name' with
  | nil =>
    cases name' with
    | nil => exact absurd rfl hne
    | cons b m =>
      have hb : b ≠ ':' := fun hb => hn' (by simp [hb])
      simp [headerLine, List.isPrefixOf, Ne.symm hb]
  | cons a n ih =>
    have ha : a ≠ ':' := fun ha => hn (by simp [ha])
    cases name' with
    | nil => simp [headerLine, List.isPrefixOf, ha]
    | cons b m =>
      by_cases hab : a = b
      · subst hab
        have hn0 : ':' ∉ n := fun h => hn (List.mem_cons_of_mem _ h)
        have hm0 : ':' ∉ m := fun h => hn' (List.mem_cons_of_mem _ h)
        have hnm : n ≠ m := fun h => hne (by rw [h])
        simpa [headerLine, List.isPrefixOf] using ih hn0 hm0 hnm
      · simp [headerLine, List.isPrefixOf, hab]

theorem valueOf_headerLine_self (name value : Text) :
    valueOf name (headerLine name value) = some (value.dropWhile Char.isWhitespace) := by
  have hdrop : (headerLine name value).drop (name.length + 1) = ' ' :: value := by
    simp [headerLine, List.drop_append]
  simp only [valueOf, isPrefixOf_headerLine_self, if_true, hdrop]
  simp

theorem valueOf_headerLine_other {name name' : Text} (hn : ':' ∉ name) (hn' : ':' ∉ name')
    (hne : name ≠ name') (value : Text) : valueOf name (headerLine name' value) = none := by
  simp [valueOf, isPrefixOf_headerLine_other hn hn' hne value]

/-- Among header lines, the reader finds the first header of that name. -/
theorem findSome_header_lines {name : Text} (hn : ':' ∉ name) {hs : List (Text × Text)}
    (h : HeadersOk hs) :
    (hs.map (fun h => headerLine h.1 h.2)).findSome? (valueOf name) =
      (hs.find? (fun h => h.1 == name)).map (fun h => h.2.dropWhile Char.isWhitespace) := by
  induction hs with
  | nil => simp
  | cons hd tl ih =>
    have htl : HeadersOk tl := fun x hx => h x (by simp [hx])
    by_cases heq : hd.1 = name
    · have hv : valueOf name (headerLine name hd.2) = some (hd.2.dropWhile Char.isWhitespace) :=
        valueOf_headerLine_self name hd.2
      simp [heq, hv]
    · have hv : valueOf name (headerLine hd.1 hd.2) = none :=
        valueOf_headerLine_other hn (h hd (by simp)).1.1 (Ne.symm heq) hd.2
      simp [hv, heq, ih htl]

/-- **The corrected reader reads headers only.** On a file whose header names and
values hold no line break, it returns the first header of that name, whatever
the body says. -/
theorem hdrBlock_file {name : Text} (hn : ':' ∉ name) {hs : List (Text × Text)}
    (h : HeadersOk hs) (body : Text) :
    hdrBlock name (file hs body) =
      (hs.find? (fun h => h.1 == name)).map (fun h => h.2.dropWhile Char.isWhitespace) := by
  rw [hdrBlock, lines_file h body, takeWhile_header_lines, findSome_header_lines hn h]

/-- The body plays no part. -/
theorem hdrBlock_file_body {name : Text} (hn : ':' ∉ name) {hs : List (Text × Text)}
    (h : HeadersOk hs) (body body' : Text) :
    hdrBlock name (file hs body) = hdrBlock name (file hs body') := by
  rw [hdrBlock_file hn h, hdrBlock_file hn h]

/-! ## One line per value -/

/-- The client's `head -1 | tr -d '\r'`: the value up to its first line feed,
without carriage returns. -/
def oneLine (v : Text) : Text := (v.takeWhile (· != '\n')).filter (· != '\r')

theorem newline_not_mem_takeWhile (v : Text) : '\n' ∉ v.takeWhile (· != '\n') := by
  induction v with
  | nil => simp
  | cons c cs ih =>
    by_cases hc : c = '\n'
    · simp [hc]
    · simp [hc, ih, Ne.symm hc]

theorem newline_not_mem_oneLine (v : Text) : '\n' ∉ oneLine v := by
  intro hm
  simp only [oneLine, List.mem_filter] at hm
  exact newline_not_mem_takeWhile v hm.1

theorem cr_not_mem_oneLine (v : Text) : '\r' ∉ oneLine v := by
  intro hm
  simp only [oneLine, List.mem_filter] at hm
  simp at hm

/-! ## The watcher on the file the client writes -/

/-- A registry name the archive keeps as one word: nonempty, with no blank or
colon. -/
def CleanName (s : String) : Prop := s.toList ≠ [] ∧ ∀ c ∈ s.toList, ¬ c.isWhitespace ∧ c ≠ ':'

/-- `<key@nostr>`, the address after the name. -/
def address (k : PubKey) : Text := '<' :: oneLine k.toList ++ ['@', 'n', 'o', 's', 't', 'r', '>']

/-- The headers the client writes that the watcher reads, with the subject the
sender chooses: `From: name <key@nostr>`, `Subject:`, and the letter's type. -/
def headersOf (reg : Registry) (e : Event) (l : Letter) : List (Text × Text) :=
  [(nameFrom, (render reg e l).originator.toList ++ ' ' :: address e.pubkey),
   (nameSubject, oneLine l.subject.toList)] ++
  (l.type.map fun t => (nameType, oneLine t.toList)).toList

/-- The archived file of a kept message. -/
def archive (reg : Registry) (e : Event) (l : Letter) : Text :=
  file (headersOf reg e l) l.body.toList

/-- The sender the watcher reads: the first word of `From:`. -/
def watcherFrom (t : Text) : Option Text := (hdrBlock nameFrom t).map (List.takeWhile (· != ' '))

/-- The type the watcher reads. -/
def watcherType (t : Text) : Option Text := hdrBlock nameType t

theorem newline_not_mem_address (k : PubKey) : '\n' ∉ address k := by
  simp [address, newline_not_mem_oneLine]

theorem headersOf_ok {reg : Registry} {e : Event} {l : Letter}
    (ho : CleanName (render reg e l).originator) : HeadersOk (headersOf reg e l) := by
  have hnl : '\n' ∉ (render reg e l).originator.toList := fun hm =>
    (ho.2 '\n' hm).1 (by decide)
  intro h hh
  simp only [headersOf, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hh
  rcases hh with (rfl | rfl) | ht
  · exact ⟨nameFrom_ok, by simp [hnl, newline_not_mem_address]⟩
  · exact ⟨nameSubject_ok, newline_not_mem_oneLine _⟩
  · cases hl : l.type with
    | none => simp [hl] at ht
    | some t =>
      simp [hl] at ht
      subst ht
      exact ⟨nameType_ok, newline_not_mem_oneLine _⟩

/-- **The type is the sealed letter's.** Whatever the body and the subject say,
the type the watcher reads from the file the client writes is the letter's own. -/
theorem watcherType_archive {reg : Registry} {e : Event} {l : Letter}
    (ho : CleanName (render reg e l).originator) :
    watcherType (archive reg e l) =
      l.type.map (fun t => (oneLine t.toList).dropWhile Char.isWhitespace) := by
  rw [watcherType, archive, hdrBlock_file nameType_ok.1 (headersOf_ok ho)]
  cases hl : l.type <;> simp [headersOf, hl, nameFrom, nameSubject, nameType]

theorem dropWhile_word {w rest : Text} (hw : w ≠ []) (hws : ∀ c ∈ w, ¬ c.isWhitespace) :
    (w ++ rest).dropWhile Char.isWhitespace = w ++ rest := by
  cases w with
  | nil => exact absurd rfl hw
  | cons c cs =>
    have hc : c.isWhitespace = false := by simpa using hws c (by simp)
    simp [hc]

theorem takeWhile_word {w rest : Text} (hws : ∀ c ∈ w, c ≠ ' ') :
    (w ++ ' ' :: rest).takeWhile (· != ' ') = w := by
  induction w with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ ' ' := hws c (by simp)
    simp [hc, ih (fun x hx => hws x (by simp [hx]))]

/-- **The sender is the archived originator.** -/
theorem watcherFrom_archive {reg : Registry} {e : Event} {l : Letter}
    (ho : CleanName (render reg e l).originator) :
    watcherFrom (archive reg e l) = some (render reg e l).originator.toList := by
  have hws : ∀ c ∈ (render reg e l).originator.toList, ¬ c.isWhitespace := fun c hc =>
    (ho.2 c hc).1
  have hsp : ∀ c ∈ (render reg e l).originator.toList, c ≠ ' ' := fun c hc h =>
    (ho.2 c hc).1 (by rw [h]; decide)
  have hfind : (headersOf reg e l).find? (fun h => h.1 == nameFrom) =
      some (nameFrom, (render reg e l).originator.toList ++ ' ' :: address e.pubkey) := by
    simp [headersOf]
  rw [watcherFrom, archive, hdrBlock_file nameFrom_ok.1 (headersOf_ok ho), hfind]
  simp only [Option.map_some]
  rw [dropWhile_word ho.1 hws, takeWhile_word hsp]

/-- **Control mail from the parent is the parent's.** If the watcher reads a kept
message as from the parent, whose key is uncompromised, and reads a type in it,
then the parent composed the message and sealed that type in it. -/
theorem watcher_control_sound {P : Primitives} (A : Authorship P) (cf : P.CollisionFree)
    {opener : Opener} {reg : Registry} (hu : (reg.map Prod.fst).Nodup)
    (hclean : ∀ m ∈ reg, CleanName m.1) {me : PubKey} {e : Event} {l : Letter}
    (ha : accept P opener reg me e = some l) {parent : String} {k : PubKey}
    (hk : (parent, k) ∈ reg) (hc : ¬ A.compromised k) {t : Text}
    (hfrom : watcherFrom (archive reg e l) = some parent.toList)
    (htype : watcherType (archive reg e l) = some t) :
    A.authored e.toUnsigned ∧
      ∃ s, l.type = some s ∧ t = (oneLine s.toList).dropWhile Char.isWhitespace := by
  obtain ⟨-, -, -, n, hn⟩ := accept_some ha
  have hmem : (n, e.pubkey) ∈ reg := nameOf_some hn
  have horig : (render reg e l).originator = n := by simp [render, hn]
  have ho : CleanName (render reg e l).originator := horig ▸ hclean _ hmem
  have hsame : (render reg e l).originator = parent := by
    rw [watcherFrom_archive ho] at hfrom
    exact String.toList_inj.mp (Option.some.inj hfrom)
  refine ⟨(no_impersonation A cf hu ha hsame hk hc).2, ?_⟩
  rw [watcherType_archive ho] at htype
  cases hl : l.type with
  | none => simp [hl] at htype
  | some s => exact ⟨s, rfl, by simpa [hl] using htype.symm⟩

/-! ## The `From:` name -/

/-- The render as first written: the `From:` name is the event's own `from_name`
tag when it has one. -/
def renderTrustingTag (reg : Registry) (e : Event) (l : Letter) : Mail.Message :=
  { render reg e l with
    originator := ((tagValues e.tags "from_name").head?).getD ((nameOf reg e.pubkey).getD "unknown") }

/-- The tag named whoever its author chose, whatever key signed. -/
theorem renderTrustingTag_forges (reg : Registry) (e : Event) (l : Letter) {n : String}
    (h : (tagValues e.tags "from_name").head? = some n) :
    (renderTrustingTag reg e l).originator = n := by
  simp [renderTrustingTag, h]

/-- The name the client renders now is a function of the signing key: no tag can
change it. -/
theorem render_originator_ignores_tags (reg : Registry) (e : Event) (l : Letter)
    (tags : List Tag) : (render reg { e with tags := tags } l).originator = (render reg e l).originator :=
  rfl

end Mettapedia.Protocols.Nostr.Archive
