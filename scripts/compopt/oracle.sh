#!/usr/bin/env bash
# lane compopt: memory policy with oracle slot sizes (what growable intern tables would give):
# records 2^27 words, memo tables 2^16 words + flush, slot tables at the smallest size that accepts
f="${@: -1}"
case "$(basename "$f")" in
  complete_c03d_pi_depth_1030.ndjson) k=22;;
  let-ladder.ndjson|complete_c04a_restart_70.ndjson|init435.ndjson) k=24;;
  beta-ladder.ndjson) k=25;;
  init-prelude.ndjson) k=20;;
  *) k=16;;
esac
M="24,41,47,48,49,50,51,52,53,54,75,76,96,97,98,99,100,101,102,103,104,105,106,146,147,148,149,150,151,152,153,155,201,202,203,204,205,206,207"
SL="3 5 7 9 11 13 15 17 19 21 23 28 30 36 38 72 73 74"
sizes=$(for a in $SL; do printf "%s=%s," $a $((1<<k)); done)
CA_SIZES=$sizes CA_SMALL=$M CA_SMALL_WORDS=65536 CA_WORDS=$((1<<27)) exec "${CA_BIN:?set CA_BIN to a binary built from the flush program (progedit.py flush) and scripts/e2e.c}" "$@"
