#!/usr/bin/env bash
# scripts/mq-next.sh: the merge queue's `next` step (scripts/mq.py has the details; PLAN.md, "Landing").
exec python3 "$(dirname "${BASH_SOURCE[0]}")/mq.py" next "$@"
