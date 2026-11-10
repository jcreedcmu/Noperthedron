"""Compile generated Lean modules and record measured costs, failing on any error."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('pattern')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--missing-only', action='store_true', help='Build only modules without an olean')
    args = parser.parse_args()
    directory = args.directory.resolve()
    files = sorted(directory.glob(args.pattern))
    if args.missing_only:
        files = [p for p in files if not p.with_suffix('.olean').exists()]
    if not files:
        raise ValueError('No matching Lean modules')
    env = os.environ.copy()
    env['LEAN_PATH'] = str(directory) + (':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    # Lake prepends its build directory to inherited LEAN_PATH. Override the
    # resolved path *inside* lake env so fresh generated modules take precedence
    # over older cached modules with the same names (notably the baseline).
    lake_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],env=env,text=True).strip()
    generated_path = str(directory)+':'+lake_path
    started = time.monotonic()

    def run(path):
        log, timing = path.with_suffix('.build.log'), path.with_suffix('.build.time')
        with log.open('w') as out:
            proc = subprocess.run(['/usr/bin/time','-f','%e %U %S %M','-o',str(timing),
                                   'lake','env','env','LEAN_PATH='+generated_path,
                                   'lean','-R',str(directory),'-o',str(path.with_suffix('.olean')),
                                   str(path)],env=env,stdout=out,stderr=subprocess.STDOUT)
        if proc.returncode:
            raise RuntimeError(f'{path}: {log.read_text()[-3000:]}')
        wall,user,system,rss = map(float,timing.read_text().split())
        return dict(file=path.name,wall=wall,cpu=user+system,rss_kib=int(rss),
                    source_bytes=path.stat().st_size,olean_bytes=path.with_suffix('.olean').stat().st_size)

    rows=[]
    failures=[]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for future in as_completed([pool.submit(run,path) for path in files]):
            try:
                rows.append(future.result())
            except Exception as error:
                failures.append(str(error))
                print(str(error),flush=True)
                continue
            if len(rows)%10 == 0 or len(rows) == len(files):
                print(f'{len(rows)}/{len(files)}: {rows[-1]}',flush=True)
    report=dict(jobs=args.jobs,wall=time.monotonic()-started,cpu_seconds=sum(r['cpu'] for r in rows),
                source_bytes=sum(r['source_bytes'] for r in rows),
                olean_bytes=sum(r['olean_bytes'] for r in rows),
                max_rss_kib=max((r['rss_kib'] for r in rows),default=0),modules=rows,failures=failures)
    args.report.write_text(json.dumps(report,indent=2)+'\n')
    print({k:v for k,v in report.items() if k!='modules'},flush=True)
    if failures:
        raise RuntimeError(f'{len(failures)} generated modules failed; see {args.report}')


if __name__ == '__main__':
    main()
