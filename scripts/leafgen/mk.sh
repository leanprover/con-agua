#!/usr/bin/env bash
# mk.sh NAME FLAGS : emit NAME.s with FLAGS (from a snapshot of LGEmit.lean), build NAME.bin, count Init instructions, check verdicts vs base
N=$1; FL=$2; D=/home/joachim/con-agua/_tmp/leafgen
cd /home/joachim/con-agua/_tmp/wt/leafgen
mkdir -p $D/snap; cp scripts/leafgen/LGEmit.lean $D/snap/$N.lean
scripts/lake env lean --run $D/snap/$N.lean $D/$N.s "$FL" 2>&1 | grep -v "^$\|Hint\|apply\|linter\|warning"
cd $D && cc -O2 -o $N.bin ../../main.c $N.s 2>/dev/null || exit 1
perf stat -e instructions:u -x, -o $N.stat ./$N.bin ../fixtures/init/init435.ndjson
echo "$N init $(grep instr $N.stat | cut -d, -f1)"
[ -n "$NOVERD" ] && exit 0
tools/verd.sh ./base.bin ./$N.bin > $N.verd
echo "$N verdict diffs: $(wc -l < $N.verd)"; head -5 $N.verd
