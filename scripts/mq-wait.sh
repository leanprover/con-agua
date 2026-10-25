#!/usr/bin/env bash
# scripts/mq-wait.sh: the merge queue's `wait` step (scripts/mq.py has the details; PLAN.md, "Landing").
exec python3 "$(dirname "${BASH_SOURCE[0]}")/mq.py" wait "$@"
