#!/bin/bash
# Export the full certificate in the root order of `Cayley.rootBox`.
# Certificate (245,484 leaves):
#   LOOK=1 NL=5 QS=12 WIDE=1 NS=12 AMAX=0.12 NA=6 BERN=1 ./export_all.sh DIR
set -e
B=./target/release/cayley-search
D=${1:-out}
mkdir -p $D
i=0
for c in 1 2 3; do OUT=$D/root$i.txt $B $c 0  0 1  0 0.5  -1 1  -1 1  -1 1  50 10 | head -1; i=$((i+1)); done
for f in 0 1 2 3 4 5; do OUT=$D/root$i.txt $B 0 $f  0 1  0 0.5  -1 1  -1 1  0 1  50 10 | head -1; i=$((i+1)); done
for f in 0 1 2 3 4 5; do OUT=$D/root$i.txt $B 4 $f  0 1  0 0.5  -1 1  -1 1  0 2  50 10 | head -1; i=$((i+1)); done
cat $(for j in $(seq 0 14); do echo $D/root$j.txt; done) > $D/cover.txt
ls -la $D/cover.txt
