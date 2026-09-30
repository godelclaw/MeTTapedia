#!/usr/bin/env python3
"""Encode saved rotations and source witnesses for the Lean kernel checker.

The emitter is untrusted: the generated declarations check every rotation,
source word, vertex inverse and opposite dart. No target colouring is stored.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

from alternating_lobe_probe import data

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
LEAN = REPO / "lean/mettapedia/Mettapedia/GraphTheory/FourColor"
if not __debug__:
    raise SystemExit("Run without Python optimization: input checks use assertions.")


def u16(values):
    result = []
    for value in values:
        assert 0 <= value < 65536
        result.extend((value % 256, value // 256))
    return result


def byte_table(name, values):
    lines = [f"def {name} : ByteArray := ByteArray.mk #["]
    lines.extend("  " + ", ".join(map(str, values[i:i + 32])) +
                 ("," if i + 32 < len(values) else "")
                 for i in range(0, len(values), 32))
    lines.append("]")
    return "\n".join(lines) + "\n\n"


def paged_table(name, values):
    assert len(values) % 2 == 0
    out = ""
    pages = (len(values) + 127) // 128
    for page in range(pages):
        out += byte_table(f"{name}Page{page}", values[128 * page:128 * (page + 1)])
    out += f"def {name} : Table where\n  size := {len(values) // 2}\n"
    out += "  pages p := match p with\n"
    for page in range(pages):
        out += f"    | {page} => {name}Page{page}\n"
    return out + "    | _ => ByteArray.empty\n\n"


def rotation_tables(rotation):
    rows = [[int(v) for v in row.split(",")] for row in rotation.split(";")]
    assert all(len(row) == len(set(row)) == 3 for row in rows)
    darts = [(u, v) for u, row in enumerate(rows) for v in row]
    positions = {d: i for i, d in enumerate(darts)}
    edges = sorted({tuple(sorted(d)) for d in darts})
    numbers = {e: i for i, e in enumerate(edges)}
    incidence = [numbers[tuple(sorted(d))] for d in darts]
    mates = [positions[v, u] for u, v in darts]
    representatives = [positions[u, v] for u, v in edges]
    assert all(mates[mates[i]] == i and incidence[mates[i]] == incidence[i]
               for i in range(len(darts)))
    return dict(vertices=len(rows), edges=len(edges), darts=darts, rows=rows,
                neighbours=u16(v for row in rows for v in row),
                incidence=u16(incidence), mates=u16(mates),
                representatives=u16(representatives))


def emit_pair(source, target, word, number):
    s, t = (rotation_tables(m["rotation"]) for m in (source, target))
    _, alpha, rho, faces = data(source["rotation"])
    face_of = {d: i for i, face in enumerate(faces) for d in face}
    labels = sorted({(face_of[d], face_of[alpha[d]]) for d in alpha})
    label_index = {label: i for i, label in enumerate(labels)}
    forward = [label_index[face_of[d], face_of[alpha[d]]] for d in s["darts"]]
    assert len(set(forward)) == len(forward) == t["vertices"]
    backward = [forward.index(v) for v in range(t["vertices"])]
    offsets = [t["rows"][forward[i]].index(forward[s["darts"].index(alpha[d])])
               for i, d in enumerate(s["darts"])]
    phi = {d: rho[alpha[d]] for d in alpha}
    previous = {v: k for k, v in phi.items()}
    for i, d in enumerate(s["darts"]):
        expected = [forward[s["darts"].index(e)] for e in (alpha[d], phi[d], previous[d])]
        assert [t["rows"][forward[i]][(offsets[i] + j) % 3] for j in range(3)] == expected
    out = f"namespace Residual{number}\n\n"
    out += f"-- {source['id']} -> {target['id']}\n"
    for role, m, c in (("source", source, s), ("target", target, t)):
        out += f"-- {role} rotation SHA-256: {hashlib.sha256(m['rotation'].encode()).hexdigest()}\n"
        for field in ("neighbours", "incidence", "mates", "representatives"):
            out += paged_table(role + field.capitalize(), c[field])
        out += (f"def {role} : CubicRotationByteCertificate.Code {c['vertices']} {c['edges']} where\n"
                f"  neighbours := {role}Neighbours\n  edges := {role}Incidence\n"
                f"  mates := {role}Mates\n  representatives := {role}Representatives\n\n"
                f"theorem {role}_valid : {role}.Valid := by decide +kernel\n\n")
    out += byte_table("colourWord", list(map(int, word)))
    out += "theorem source_word_proper : ProperWord source colourWord := by decide +kernel\n\n"
    out += paged_table("forward", u16(forward))
    out += paged_table("backward", u16(backward))
    out += paged_table("offsets", u16(offsets))
    out += (f"def adapter : Adapter {s['vertices']} {t['vertices']} where\n"
            "  forward := forward\n  backward := backward\n  offsets := offsets\n\n"
            "theorem adapter_valid : adapter.Valid := by decide +kernel\n\n"
            "theorem adapter_compatible : adapter.Compatible source source_valid target := by\n"
            "  decide +kernel\n\n"
            "theorem target_tait : RotationSystemTaitColorable (target.rotation target_valid) :=\n"
            "  adapter.tait source source_valid target adapter_valid target_valid\n"
            "    adapter_compatible colourWord source_word_proper\n\n"
            f"theorem target_supported_route (order : List (Fin {t['vertices']}))\n"
            "    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ v, visited order v) :\n"
            "    ∃ cyclic : VertexRotationCyclic (target.rotation target_valid),\n"
            "      VertexConstructionGSLT.colouring.Supports\n"
            "        (route (encodeClosed (target.cubic target_valid) cyclic order hn he hcover).trace)\n"
            "        Fin.elim0 Fin.elim0 :=\n"
            "  adapter.supported_route_exists source source_valid target adapter_valid target_valid\n"
            "    adapter_compatible colourWord source_word_proper order hn he hcover\n\n"
            f"end Residual{number}\n\n")
    return out


def generate(only=None):
    witnesses = json.loads((HERE / "dual-truncate-colouring-fixtures.json").read_text())["maps"]
    sources = {m["id"]: m for m in json.loads((HERE / "family-supply-fixtures.json").read_text())["maps"]}
    targets = {m["id"]: m for m in json.loads((HERE / "family-supply-probe.json").read_text())["maps"]}
    header = ("/-! A compact input certificate for one of the five saved residual maps.\n"
           "The kernel checks source and target rotations, source colour words,\n"
           "and exact construction adapters. All target colourings use the\n"
           "uniform local reconstruction; no target colouring table is retained.\n"
           "Generated by `generate_dual_truncate_certificates.py`. -/\n\n"
           "set_option maxRecDepth 100000\nset_option maxHeartbeats 20000000\n\n"
           "namespace Mettapedia.GraphTheory.FourColor.DualTruncateResidualCertificates\n\n"
           "open CubicRotationByteCertificate DualTruncateByteCertificate\n"
           "open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceDualConnectedness\n"
           "open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace\n"
           "open VertexConstructionGSLT\n\n")
    files = {}
    for number, w in enumerate(witnesses):
        if only is None or number == only:
            dependency = "DualTruncateByteCertificate" if number == 0 else f"DualTruncateResidualCertificate{number - 1}"
            out = f"import Mettapedia.GraphTheory.FourColor.{dependency}\n\n" + header
            out += emit_pair(sources[w["source"]], targets[w["target"]], w["vertex_colour_word"], number)
            out += "end Mettapedia.GraphTheory.FourColor.DualTruncateResidualCertificates\n"
            files[f"DualTruncateResidualCertificate{number}.lean"] = out
    if only is None:
        files["DualTruncateResidualCertificates.lean"] = (
            "import Mettapedia.GraphTheory.FourColor.DualTruncateResidualCertificate4\n\n"
            "/-! Kernel-certified compact inputs for the five saved residual maps.\n"
            "The independent certificates share one decoder and reconstruction law.\n"
            "Their imports are ordered to bound certificate evaluation costs. -/\n")
    return files


def decoded_table(text, name):
    """Read emitted byte literals independently of the text emitter."""
    matches = re.findall(r"def " + name + r"Page(\d+) : ByteArray := ByteArray.mk #\[(.*?)\]",
                         text, re.S)
    assert [int(page) for page, _ in matches] == list(range(len(matches)))
    payload = [int(v) for _, body in matches for v in re.findall(r"\d+", body)]
    assert all(0 <= v < 256 for v in payload) and len(payload) % 2 == 0
    return [payload[i] + 256 * payload[i + 1] for i in range(0, len(payload), 2)]


def check_input_identity(directory, only):
    witnesses = json.loads((HERE / "dual-truncate-colouring-fixtures.json").read_text())["maps"]
    sources = {m["id"]: m for m in json.loads((HERE / "family-supply-fixtures.json").read_text())["maps"]}
    targets = {m["id"]: m for m in json.loads((HERE / "family-supply-probe.json").read_text())["maps"]}
    replay = {m["target"]: m for m in json.loads((HERE / "dual-truncate-colouring.json").read_text())["maps"]}
    for number, w in enumerate(witnesses):
        if only is not None and number != only:
            continue
        text = (directory / f"DualTruncateResidualCertificate{number}.lean").read_text()
        source_rows = [[int(v) for v in r.split(",")] for r in sources[w["source"]]["rotation"].split(";")]
        for role, record in (("source", sources[w["source"]]), ("target", targets[w["target"]])):
            rows = [[int(v) for v in r.split(",")] for r in record["rotation"].split(";")]
            assert decoded_table(text, role + "Neighbours") == [v for row in rows for v in row]
            assert replay[w["target"]][role + "_rotation_sha256"] == hashlib.sha256(record["rotation"].encode()).hexdigest()
        raw_word = re.search(r"def colourWord : ByteArray := ByteArray.mk #\[(.*?)\]", text, re.S)
        assert raw_word is not None
        assert [int(v) for v in re.findall(r"\d+", raw_word[1])] == list(map(int, w["vertex_colour_word"]))
        sorted_darts = sorted((u, v) for u, row in enumerate(source_rows) for v in row)
        vertex_map = dict(zip(sorted_darts, map(int, replay[w["target"]]["vertex_adapter_word"].split(","))))
        assert decoded_table(text, "forward") == [vertex_map[u, v] for u, row in enumerate(source_rows) for v in row]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=LEAN)
    parser.add_argument("--only", type=int, choices=range(5), help="Encode one representative pair for measurement.")
    parser.add_argument("--check", action="store_true", help="Check generated files without changing them.")
    args = parser.parse_args()
    files = generate(args.only)
    for name, content in files.items():
        path = args.output_dir / name
        if args.check:
            assert path.read_text() == content, f"Generated certificate differs: {name}"
        else:
            path.write_text(content)
    if args.check:
        check_input_identity(args.output_dir, args.only)
    print(json.dumps(dict(pairs=5 if args.only is None else 1, source_bytes=sum(len(s.encode()) for s in files.values()))))


if __name__ == "__main__":
    main()
