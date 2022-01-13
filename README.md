# Advent of Code 2021 in Idris2

Some Advent of Code solutions in idris2.

## Highlights

+ Minimal idris2 benchmarking framework (https://github.com/phlip9/idris2-aoc21/blob/master/src/Bench.idr)

+ Formally verified `Vect.windows n` (https://github.com/phlip9/idris2-aoc21/blob/master/src/Scratch.idr#L209)

## Setup

Install `nix` (https://nixos.org/download.html)

## Run

Run an Advent of Code day

```bash
$ ./x run day 3 data/03
```

Type check

```bash
$ ./x check
```

Open the idris2 repl and load a source file

```bash
$ ./x repl
Main> :load "src/Data/Vec.idr"
Data.Vec>
```

Run the property tests

```bash
$ ./x test
```

Run the benchmarks

```bash
$ ./x run bench

Bench Group: sum List
━━━━━━━━━━━━━━━━━━━━━
bench   sum List/inline:                101.83 µs (± 6.11 µs)

Bench Group: sum IOVec
━━━━━━━━━━━━━━━━━━━━━━
bench   sum IOVec/IO:                   418.74 µs (± 20.17 µs)
bench   sum IOVec/unsafeIO:             184.69 µs (± 2.30 µs)
bench   sum IOVec/unsafeIO spec:        160.12 µs (± 2.01 µs)
bench   sum IOVec/unsafeIO spec,inl:    159.82 µs (± 2.40 µs)
bench   sum IOVec/unsafeIO spec,inl,get: 161.20 µs (± 2.58 µs)

Bench Group: sum IOVec
━━━━━━━━━━━━━━━━━━━━━━
bench   sum IOVec/pure spec,inl:        161.05 µs (± 3.16 µs)

Bench Group: sum I61Vec
━━━━━━━━━━━━━━━━━━━━━━━
bench   sum I61Vec/pure spec,inl:        11.50 µs (± 140 ns)
```
