#!/usr/bin/env bash
# bisect.sh FLAGS FIXTURE N : find the single function index whose new code breaks FIXTURE
FL=$1; FX=$2; lo=0; hi=$3
cd /home/joachim/p/con-agua/_tmp/wt/leafgen
want=$(/home/joachim/p/con-agua/_tmp/leafgen/base.bin $FX | head -1)
while [ $((hi - lo)) -gt 1 ]; do
  mid=$(( (lo + hi) / 2 ))
  scripts/lake -d x86 env lean --run scripts/leafgen/LGEmit.lean /home/joachim/p/con-agua/_tmp/leafgen/bis.s "$FL" $lo $mid >/dev/null 2>&1
  cc -O2 -I/home/joachim/p/con-agua/commons --embed-dir=/home/joachim/p/con-agua/commons -o /home/joachim/p/con-agua/_tmp/leafgen/bis.bin /home/joachim/p/con-agua/commons/main.c /home/joachim/p/con-agua/_tmp/leafgen/bis.s 2>/dev/null
  got=$(timeout 60 /home/joachim/p/con-agua/_tmp/leafgen/bis.bin $FX | head -1)
  if [ "$got" != "$want" ]; then hi=$mid; else lo=$mid; fi
  echo "range $lo $hi" >&2
done
echo "first bad index $lo"
