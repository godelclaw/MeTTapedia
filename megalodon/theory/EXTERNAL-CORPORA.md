# External Megalodon theory corpora — not vendored here

Two large third-party corpora are **referenced, not stored** in this repository.
They are kept out of version control (see `.gitignore`) because they are external
work without a clear redistribution license in their source. Fetch them locally if
you need them; the rest of `megalodon/theory/` (original / attributed developments)
stays tracked.

## `megalodon/theory/numbers/` — Chad E. Brown's *FormalNumbers*
- ~5,800 files (rendered HTML of a large Megalodon number-theory development).
- Source: Chad E. Brown's Megalodon pages — <http://grid01.ciirc.cvut.cz/~chad/>
  (and the Proofgold ecosystem). Upstream Megalodon: <https://github.com/ai4reason/Megalodon> (MIT).

## `megalodon/theory/atp/` — Proofgold / mgw_test AIM-bounty problems
- ~1,018 TPTP `.p` files; headers link `https://mgwiki.github.io/mgw_test/...`.
- Source: the `mgw_test` wiki corpus — <https://github.com/mgwiki/mgw_test>
  and <https://prfgld.github.io/>. No top-level redistribution LICENSE found, so it
  is not republished here.

## Kept in-repo (original / attributed, small)
`mizar/` (original Megalodon developments), `logic/GoedelGod.mg` (attributed
Benzmüller/Woltzenlogel-Paleo port), `ramsey/`, `metamath/`, `category/`, `surreals/`.

If/when provenance + licensing are settled, any of the above can be re-added
deliberately. Until then: reference, don't vendor.
