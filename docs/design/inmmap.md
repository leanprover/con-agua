# inmmap: map the input, fall back to slurp

User decision (2026-10-25): "mmap, fall back to slurp". `main.c`'s `read_input` opens FILE; a nonempty
regular file is mapped `PROT_READ, MAP_PRIVATE` (length = `st_size`, an `off_t`, so below 2^63);
anything else (pipe, terminal, `/dev/null`, an empty or size-0 regular file such as `/proc` files) or a
refused mmap goes to `slurp`, which now takes the open fd. `run_jobs` unmaps instead of freeing a
mapped buffer (`in_mapped`). A file changed by another process during the run is outside the theorem
("you break it, you keep it"); a truncated one faults (SIGBUS), never an accept.

No `madvise(MADV_SEQUENTIAL)`: the inputs are normally in the page cache, and the measurements below
are too noisy (load ~200-240 on 96 cores) to show any effect of it.

## Checks
- `make check` ok; `diff-e2e.py --parallel 16`: 628/628 agree, sequential and `--jobs 4`.
- pipe (`cat f | ./checker /dev/stdin`, also `--jobs=4`): accept, reads via `slurp` (strace);
  `< f` redirect is a regular file and is mapped; empty file and `/dev/null`: accept, as before;
  a directory or missing file: status 3 with a message, as before.

## Measurements (2026-10-25, load ~200-240 on 96 cores)
RSS: `ru_maxrss` counts file-backed pages of the mapping, which are clean and reclaimable; the
anonymous part (`RssAnon`, sampled every 50 ms) is what the input no longer costs.

Init (`init435.ndjson`, 346 MB), 3 interleaved rounds, medians:

| mode | binary | wall | ru_maxrss | peak RssAnon | peak RssFile |
|---|---|---:|---:|---:|---:|
| sequential | old | 72.2 s | 736 MB | 741 MB | 3 MB |
| sequential | new | 69.1 s | 737 MB | 410 MB | 333 MB |
| `--jobs=4` | old | 22.4 s | 999 MB | 985 MB | 4 MB |
| `--jobs=4` | new | 22.0 s | 994 MB | 646 MB | 333 MB |

Mathlib (`mathlib.ndjson`, 6.2 GB), `--jobs=4`, two rounds (old-new, then new-old), under a 24 GB cap:

| binary | wall | ru_maxrss | peak RssAnon | peak RssFile |
|---|---:|---:|---:|---:|
| old | 521 s, 570 s | 16.0, 16.2 GB | 16.0, 16.2 GB | 4 MB |
| new | 578 s, 588 s | 9.8, 10.3 GB | 9.3, 9.7 GB | 1.4, 1.0 GB |

Mathlib's peak anonymous memory drops by about 6.5 GB (the input), and so does `ru_maxrss` (the file
pages are partly evicted as the run goes on). Wall time is 3-11% slower in these two rounds; the old
binary alone varied by 9% between rounds, so this is not established either way.
