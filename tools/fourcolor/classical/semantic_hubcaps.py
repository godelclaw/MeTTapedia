"""Generate semantic hubcaps from symmetric single-edge and paired certificates.

This generator is untrusted: every retained computation, part identity,
transport and consuming coverage proof is checked by Lean. Bounds must agree;
paired inputs transport both their part and their relative endpoint offset.
"""

from collections import defaultdict
from functools import lru_cache
import re

from reflection_candidates import inspect_arity, parse_part, read_queries, reflect, rotate
from paired_charge_candidates import inspect_arity as inspect_pairs
from paired_charge_candidates import pair_orbit, read_paired_queries


@lru_cache(maxsize=None)
def selected_cases(reference, n=10):
    """The remaining reflection candidates within individual hubcaps."""
    inventories = [inspect_arity(reference, n), inspect_pairs(reference, n)]
    selected = set()
    for inventory in inventories:
        for group in inventory["new_groups"]:
            cases = {int(name.split("_")[1]) for name in group}
            if len(cases) != 1:
                raise ValueError("Cross-hubcap sharing needs a separate dependency plan")
            selected.update(cases)
    # These two cases already have separately audited uniform consumers.
    if n == 10:
        selected.difference_update((128, 242))
    data = (reference / f"FourColor/Present{n}Defs.lean").read_text()
    parts = {name: parse_part(body) for name, body in
             re.findall(r"^def (\w+) : Part := (.*)$", data, re.M)}
    rows, _ = read_queries(reference, n)
    pair_rows, _, _ = read_paired_queries(reference, n)
    pairs = {row["name"]: row for row in pair_rows}
    by_case = defaultdict(list)
    for row in rows:
        case = int(row["name"].split("_")[1])
        if case not in selected:
            continue
        expression = " ".join(row["expression"].split())
        match = re.fullmatch(
            rf"(checkDbound2|check2Dbound2) theRedpart rf{n} "
            rf"\((hubcapRot {n} (\d+) (\w+))\) (.*)", expression)
        if not match:
            raise ValueError("Unrecognized selected check: " + expression)
        kind, part_expression, j, part_name, tail = match.groups()
        item = dict(row, expression=expression, kind=kind,
                    part_expression=part_expression, part_name=part_name,
                    index=int(j))
        if kind == "checkDbound2":
            item["bound"] = int(tail.strip("()"))
            part = rotate(parts[part_name], int(j) - 2 if int(j) >= 2 else n + int(j) - 2)
            item["part"] = part
            item["key"] = ("single", min(part, reflect(part)), item["bound"])
        else:
            item.update(pairs[row["name"]])
            item["key"] = ("pair", min(pair_orbit(item["part"], item["offset"]).values()),
                           item["bound"])
        by_case[case].append(item)
    result = {}
    for case in sorted(selected):
        queries = sorted(by_case[case], key=lambda q: int(q["name"].split("_")[-1]))
        if len({q["part_name"] for q in queries}) != 1:
            raise ValueError("A hubcap uses different parts")
        representatives = {}
        for q in queries:
            rep = representatives.setdefault(q["key"], q)
            q["representative"] = rep["name"]
            q["representative_expression"] = rep["part_expression"]
            if q["kind"] == "checkDbound2":
                q["reflected"] = q["part"] != rep["part"]
                if q["reflected"] and q["part"] != reflect(rep["part"]):
                    raise ValueError("The proposed reflection does not match")
            else:
                q["representative_offset"] = rep["offset"]
                q["transport"] = next((name for name, value in pair_orbit(
                    rep["part"], rep["offset"]).items() if value == (q["part"], q["offset"])), None)
                if q["transport"] is None:
                    raise ValueError("The proposed pair transport does not match")
        kept = [q for q in queries if q["representative"] == q["name"]]
        result[case] = dict(queries=queries, kept=kept, before=len(queries),
                            after=len(kept), part=queries[0]["part_name"])
    return result


def replace_checks(source, cases, n=10):
    """Replace each affected Boolean hubcap by semantic bounds on the same entries."""
    used = []
    for case, data in cases.items():
        name = f"f{n}_{case}"
        if not re.search(rf"^theorem {name} :", source, re.M):
            continue
        first_check = source.index(f"theorem c{n}_{case}_1 :")
        first = source.rindex("set_option maxRecDepth", 0, first_check)
        start = source.index(f"theorem {name} :")
        end = source.index("\n\n", start)
        fit = source[start:end]
        match = re.fullmatch(
            rf"theorem {name} :\s+hubcapFit theRedpart rf{n} (\w+)\s+"
            r"(\(Hubcap\..*\)) = true := by\n  simp \[hubcapFit, (.*)\]", fit, re.S)
        if not match:
            raise ValueError("Unexpected hubcap proof: " + name)
        part_name, hubcap, names = match.groups()
        if part_name != data["part"] or names.split(", ") != [q["name"] for q in data["queries"]]:
            raise ValueError("Hubcap/check correspondence differs: " + name)
        declarations = []
        for q in data["kept"]:
            declarations.append(
                "set_option maxRecDepth 100000 in\n"
                "set_option maxHeartbeats 1000000 in\n"
                f"theorem {q['name']} : {q['expression']} = true := by\n  decide +kernel")
        proof = [f"theorem {name} (hred : RedpartSound theRedpart) :",
                 f"    Hubcap.SemanticFit {n} {part_name}", f"    {hubcap} := by",
                 "  refine ⟨" + ", ".join(["?_"] * len(data["queries"]) + ["trivial"]) + "⟩"]
        for q in data["queries"]:
            rep = q["representative"]
            if q["kind"] == "check2Dbound2":
                if rep == q["name"]:
                    proof.append(f"  · exact PairChargeBound.of_check hred rf{n} rfl (by decide) {rep}")
                    continue
                operation, offset = q["transport"], q["representative_offset"]
                part = f"({q['representative_expression']})"
                target = dict(identity=part, swap=f"Part.rot {offset} {part}",
                              reflect=f"reflectDrule {part}",
                              reflect_swap=f"Part.rot ({n} - {offset}) (reflectDrule {part})")[operation]
                proof.append(f"  · rw [show {q['part_expression']} = {target} by decide +kernel]")
                if operation != "identity":
                    side_conditions = "(by decide)" if operation == "swap" else "(by decide) (by decide)"
                    proof.append(f"    apply PairChargeBound.{operation} (p := {part}) "
                                 f"(n := {n}) (j := {offset}) (b := ({q['bound']})) rfl {side_conditions}")
                proof.append(f"    exact PairChargeBound.of_check hred rf{n} rfl (by decide) {rep}")
            elif rep == q["name"]:
                proof.append(f"  · exact ChargeBound.of_check hred rf{n} rfl {rep}")
            else:
                target = f"({q['representative_expression']})"
                if q["reflected"]:
                    target = "reflectDrule " + target
                proof.append(f"  · rw [show {q['part_expression']} = {target} by decide +kernel]")
                if q["reflected"]:
                    proof.append(f"    apply ChargeBound.reflect (p := {q['representative_expression']}) "
                                 f"(b := ({q['bound']})) (by decide)")
                proof.append(f"    exact ChargeBound.of_check hred rf{n} rfl {rep}")
        declarations.append("\n".join(proof))
        source = source[:first] + "\n\n".join(declarations) + source[end:]
        used.append(case)
    if used:
        source = "import MettapediaFourColor.PairChargeTransport\n" + source
    return source, used


def replace_consumers(source, cases, n=10):
    """Retain the cover and split tree while supplying semantic certificates."""
    used = []
    pattern = (rf"exact succeed_by_hubcap{n} hred\n"
               r"(?P<hc>\s+\(Hubcap\.(?:one|two).*?Hubcap.nil\))\n"
               r"(?P<indent> +)rfl \(by decide \+kernel\) \(by decide \+kernel\) "
               rf"f{n}_(?P<case>\d+)\b")

    def replace(match):
        case = int(match["case"])
        if case not in cases:
            return match[0]
        used.append(case)
        return (f"exact Hubcap.succeeds _\n{match['hc']}\n{match['indent']}"
                f"rfl (by decide +kernel) (by decide +kernel) (f{n}_{case} hred)")

    source = re.sub(pattern, replace, source, flags=re.S)
    return source, used


def audit_source(cases, n=10):
    """Require every replacement in the endpoint and exclude each removed check."""
    removed = [q["name"] for data in cases.values() for q in data["queries"]
               if q["name"] != q["representative"]]
    lines = ["import MettapediaFourColor.OrbitAssemblyAudit", "", "open Lean Elab Command in",
             "run_cmd do", "  let env ← getEnv",
             "  for rootName in [``FourColor.OrbitAssembly.colorable_of_planeDrawing,",
             "      ``FourColor.OrbitAssembly.supported_source_construction_of_checks] do",
             "    let mut seen : NameSet := {}", "    let mut todo := [rootName]",
             "    while !todo.isEmpty do", "      let name := todo.head!", "      todo := todo.tail!",
             "      if !seen.contains name then", "        seen := seen.insert name",
             "        if let some info := env.find? name then",
             "          todo := info.getUsedConstantsAsSet.toList ++ todo"]
    for case in cases:
        lines.extend([f"    unless seen.contains ``FourColor.Orbit{n}.f{n}_{case} do",
                      f'      throwError m!"Semantic hubcap f{n}_{case} is not consumed by {{rootName}}"'])
    for name in removed:
        for prefix in ("FourColor", f"FourColor.Orbit{n}"):
            lines.extend([f"  if env.contains `{prefix}.{name} then",
                          f'    throwError "Removed check {prefix}.{name} is present"'])
    lines.append(f'  logInfo "Audited {len(cases)} semantic hubcaps in both endpoints and {len(removed)} removed checks."')
    return "\n".join(lines) + "\n"
