#!/usr/bin/env bash
# scripts/submit.sh: the merge queue's `submit` step (scripts/mq.py has the details; PLAN.md, "Landing").
exec python3 "$(dirname "${BASH_SOURCE[0]}")/mq.py" submit "$@"
