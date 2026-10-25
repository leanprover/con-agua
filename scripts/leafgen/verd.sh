#!/usr/bin/env bash
# verd.sh A.bin B.bin : compare verdicts on all e2e fixtures (timeout 60 s each)
A=$1; B=$2
ls /home/joachim/con-agua/_tmp/ref/con-leche/tests/e2e/*.ndjson | grep -v "whnf_delta_loop\|whnf_core_loop" | xargs -P 24 -I{} bash -c 'a=$(timeout 60 '$A' {} 2>/dev/null | head -1); b=$(timeout 60 '$B' {} 2>/dev/null| head -1); [ "$a" == "$b" ] || echo "DIFF {} $a / $b"'
