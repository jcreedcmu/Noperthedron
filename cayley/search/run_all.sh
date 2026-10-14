#!/bin/bash
# Full floating-point cover: charts 1-3 plain, charts 0 and 4 blown up per face.
B=./target/release/cayley-search
for c in 1 2 3; do echo "chart $c"; $B $c 0  0 1  0 0.5  -1 1  -1 1  -1 1  50 10 2>&1 | grep -E "^(nodes|FAIL)" | head -4; done
for c in 0 4; do
  R=1; [ $c = 4 ] && R=2
  for f in 0 1 2 3 4 5; do echo "chart $c face $f"; $B $c $f  0 1  0 0.5  -1 1  -1 1  0 $R  50 10 2>&1 | grep -E "^(nodes|FAIL)" | head -4; done
done
