"""Build a complete kernel proof from an alternative Noperthedron tree.

Uses the unchanged checker and soundness theorems. All generated outputs are
isolated, and success requires the final theorem's standard-axiom audit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
HARNESS = Path(__file__).with_name('build_generated.py')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--directory', type=Path, required=True)
    ap.add_argument('--leaves', type=int, default=32)
    ap.add_argument('--chunks', type=int, default=180)
    ap.add_argument('--jobs', type=int, default=8)
    args = ap.parse_args()
    out = args.directory.resolve()
    if out.exists() and any(out.iterdir()):
        raise ValueError('Use an empty or new output directory')
    out.mkdir(parents=True, exist_ok=True)
    cert = args.certificate.resolve()
    data, gen = out/'data', out/'CayleyKernel/Gen'
    start = time.monotonic()
    subprocess.run(['lake', 'build', 'cayleyCheck', 'CayleyKernel.Load',
                    'Cayley.Soundness.KMain', 'Noperthedron.MainTheorem',
                    'Noperthedron.Vertices.InteriorNonempty'], cwd=ROOT, check=True)
    subprocess.run([str(ROOT/'.lake/build/bin/cayleyCheck'), 'kgen', str(cert),
                    str(data), str(gen), str(args.leaves), str(args.chunks)], cwd=ROOT, check=True)
    for p in gen.glob('*.lean'):
        source = p.read_text().replace(str(gen).replace('/', '.'), 'CayleyKernel.Gen')
        if p.name.startswith('R'):
            source = source.replace('set_option Elab.async false',
                                    'set_option Elab.async false\nset_option maxRecDepth 100000')
        p.write_text(source)
    for name in ['Load.lean', 'Main.lean']:
        shutil.copyfile(ROOT/'CayleyKernel'/name, out/'CayleyKernel'/name)
    reports = {}
    for phase, pattern in [('loader','CayleyKernel/Load.lean'),
                           ('arithmetic','CayleyKernel/Gen/C*.lean'),
                           ('root-links','CayleyKernel/Gen/R*.lean'),
                           ('root-imports','CayleyKernel/Gen/All.lean'),
                           ('complete-proof','CayleyKernel/Main.lean')]:
        report = out/(phase+'.json')
        subprocess.run([sys.executable, str(HARNESS), str(out), pattern,
                        '--jobs', str(args.jobs), '--report', str(report)], cwd=ROOT, check=True)
        reports[phase] = json.loads(report.read_text())
    audit = (out/'CayleyKernel/Main.build.log').read_text()
    expected = "'Cayley.KProof.exists_not_rupert' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if expected not in audit:
        raise ValueError(f'Unexpected axiom audit: {audit}')
    generated = [r for k,r in reports.items() if k!='loader']
    tokens = cert.read_text().split()
    result = dict(certificate=str(cert), sha256=hashlib.sha256(cert.read_bytes()).hexdigest(),
                  certificate_bytes=cert.stat().st_size,
                  certificate_leaves=sum(t[0] in 'GD' for t in tokens),
                  gap_leaves=sum(t[0]=='G' for t in tokens),
                  domain_leaves=sum(t[0]=='D' for t in tokens),
                  chunk_leaves=args.leaves, chunks_per_module=args.chunks, jobs=args.jobs,
                  wall=time.monotonic()-start,
                  generated_cpu_seconds=sum(r['cpu_seconds'] for r in generated),
                  generated_source_bytes=sum(r['source_bytes'] for r in generated),
                  generated_olean_bytes=sum(r['olean_bytes'] for r in generated),
                  max_module_rss_kib=max(r['max_rss_kib'] for r in generated),
                  timing_scope='Generated arithmetic, root links, imports and final theorem; cached supporting proofs. Loader and generation excluded.',
                  checker_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in sorted((ROOT/'Cayley').rglob('*.lean'))},
                  axiom_audit=audit, phases=reports)
    (out/'complete-report.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'phases','checker_sha256'}},indent=2))


if __name__ == '__main__':
    main()
