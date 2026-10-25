#!/usr/bin/env bash
# CA_BIN: the binary (scripts/e2e.c + a program with `progedit.py flush`); CA_PINS: the pin data; CA_CPUS: taskset list
# print the smallest slot-table size (2^k words) at which the fixture is accepted
f=$1
M="24,41,47,48,49,50,51,52,53,54,75,76,96,97,98,99,100,101,102,103,104,105,106,146,147,148,149,150,151,152,153,155,201,202,203,204,205,206,207"
SL="3 5 7 9 11 13 15 17 19 21 23 28 30 36 38 72 73 74"
for k in $(seq 16 26); do
  sizes=$(for a in $SL; do printf "%s=%s," $a $((1<<k)); done)
  out=$(CA_SIZES=$sizes CA_SMALL=$M CA_SMALL_WORDS=65536 CA_WORDS=$((1<<27)) taskset -c "${CA_CPUS:-0}" nice timeout 600 "${CA_BIN:?set CA_BIN to a binary built from the flush program (progedit.py flush) and scripts/e2e.c}" "$f")
  if [ "$out" = "accept" ]; then echo "$k $(basename $f) $(stat -c %s $f)"; exit 0; fi
done
echo "none $(basename $f)"
