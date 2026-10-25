#!/usr/bin/env bash
# scripts/mq-status.sh: the merge queue's `status` step (scripts/mq.py has the details; PLAN.md, "Landing").
exec python3 "$(dirname "${BASH_SOURCE[0]}")/mq.py" status "$@"
