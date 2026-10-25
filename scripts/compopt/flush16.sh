#!/bin/sh
CA_SMALL=24,41,47,48,49,50,51,52,53,54,75,76,96,97,98,99,100,101,102,103,104,105,106,146,147,148,149,150,151,152,153,155,201,202,203,204,205,206,207 CA_SMALL_WORDS=65536 exec "${CA_BIN:?set CA_BIN to a binary built from the flush program (progedit.py flush) and scripts/e2e.c}" "$@"
