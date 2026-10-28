#!/usr/bin/env python3
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

GF_LD = os.environ.get('GF_LIBRARY_PATH', '')


def ensure_runtime_libs():
    if not GF_LD:
        return
    cur = os.environ.get('LD_LIBRARY_PATH', '')
    parts = [x for x in cur.split(':') if x]
    if GF_LD in parts:
        return
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = ':'.join([GF_LD] + parts)
    os.execvpe(sys.executable, [sys.executable, __file__, *sys.argv[1:]], env)


ensure_runtime_libs()

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parents[2]
ROOT = SCRIPT_DIR
GENERATED = ROOT / 'generated'
TEMP = ROOT / 'project_core_json_export'
GF_LIB = Path(
    os.environ.get('GF_RGL_ROOT', REPO_ROOT / 'lean/externals/gf-rgl')
).expanduser()
GF_BIN = os.environ.get('GF_BIN', 'gf')
MANIFEST_PATH = GENERATED / 'project_core_manifest.json'

TARGETS = [
    ('english', Path('src/english/GrammarEng.gf'), 'GrammarEng.project_core'),
    ('czech', Path('src/czech/GrammarCze.gf'), 'GrammarCze.project_core'),
]


def gf_path_arg() -> str:
    paths = [
        str(ROOT),
        str(GF_LIB / 'src' / 'abstract'),
        str(GF_LIB / 'src' / 'common'),
        str(GF_LIB / 'src' / 'prelude'),
        str(GF_LIB / 'src' / 'api'),
        str(GF_LIB / 'src' / 'english'),
        str(GF_LIB / 'src' / 'czech'),
    ]
    return ':'.join(paths)


def ensure_manifest():
    if MANIFEST_PATH.exists():
        return
    subprocess.run(['python3', 'export_project_core_manifest.py'], cwd=ROOT, check=True)


def compile_target(source_gf: Path, stem: str) -> tuple[Path, Path]:
    if TEMP.exists():
        shutil.rmtree(TEMP)
    TEMP.mkdir(parents=True, exist_ok=True)
    cmd = [
        GF_BIN,
        '--output-format=json',
        f'--output-dir={TEMP}',
        f'--path={gf_path_arg()}',
        '--make',
        str(source_gf),
    ]
    subprocess.run(cmd, cwd=ROOT, check=True, env=os.environ.copy())
    json_src = TEMP / 'Grammar.json'
    pgf_src = TEMP / 'Grammar.pgf'
    json_dst = GENERATED / f'{stem}.json'
    pgf_dst = GENERATED / f'{stem}.pgf'
    shutil.copyfile(json_src, json_dst)
    shutil.copyfile(pgf_src, pgf_dst)
    return json_dst, pgf_dst


def load_json(path: Path) -> dict:
    return json.loads(path.read_text())


def overlap_report(manifest: dict, exported: dict) -> dict:
    exported_funs = set(exported['abstract']['funs'].keys())
    project_core = manifest['scope']['projectCoreFunctions']
    project_core_plus_symbol = manifest['scope']['projectCorePlusSymbolFunctions']
    return {
        'abstractName': exported['abstract']['name'],
        'startcat': exported['abstract']['startcat'],
        'abstractFunctionCount': len(exported_funs),
        'projectCoreOverlap': len(set(project_core) & exported_funs),
        'projectCoreMissing': sorted(set(project_core) - exported_funs),
        'projectCorePlusSymbolOverlap': len(set(project_core_plus_symbol) & exported_funs),
        'projectCorePlusSymbolMissing': sorted(set(project_core_plus_symbol) - exported_funs),
        'concretes': {
            lang: {
                'productions': len(concr['productions']),
                'functions': len(concr['functions']),
                'categories': len(concr['categories']),
            }
            for lang, concr in exported['concretes'].items()
        },
    }


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    ensure_manifest()
    manifest = load_json(MANIFEST_PATH)
    report: dict[str, object] = {
        'scopeName': manifest['scope']['name'],
        'projectCoreCount': manifest['scope']['projectCoreCount'],
        'projectCorePlusSymbolCount': manifest['scope']['projectCorePlusSymbolCount'],
        'targets': {},
    }
    for label, source_rel, stem in TARGETS:
        json_out, pgf_out = compile_target(GF_LIB / source_rel, stem)
        exported = load_json(json_out)
        report['targets'][label] = {
            'source': f'$GF_RGL_ROOT/{source_rel.as_posix()}',
            'json': str(json_out.relative_to(REPO_ROOT)),
            'pgf': str(pgf_out.relative_to(REPO_ROOT)),
            'summary': overlap_report(manifest, exported),
        }
    out = GENERATED / 'project_core_export_report.json'
    out.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    print(f'wrote {out}')
    for label in ('english', 'czech'):
      summary = report['targets'][label]['summary']
      print(
          f"{label}: abstract={summary['abstractFunctionCount']} "
          f"projectCore={summary['projectCoreOverlap']}/{report['projectCoreCount']} "
          f"projectCorePlusSymbol={summary['projectCorePlusSymbolOverlap']}/{report['projectCorePlusSymbolCount']}"
      )


if __name__ == '__main__':
    main()
