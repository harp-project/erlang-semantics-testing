# Semantics-tester

This software implements property-based cross-testing of Erlang (implemented in the K framework) and Core Erlang (implemented in Coq) semantics.

Dependencies:

    xpath
        apt install libxml-xpa
    Erlang/OTP (>22)
        https://www.erlang.org/downloads
    Erlang QuickCheck (preferably Quviq, compatibility with PropEr or Triq is not tested)
        http://www.quviq.com/downloads/
    Coq (>8.12)
        https://github.com/coq/coq/releases/tag/V8.12.0
    K framework (3.6)
        https://github.com/kframework/k-legacy/releases/tag/v3.6

Supplied dependencies:

    eqc (Erlang BEAM)
    generator (Erlang BEAM)

# Setup

1. Compile the semantics:
  - Run `kompile erl.k` in the `erlang-semantics/erl_env` and `erlang-semantics/erl_env_traced`. These folders include the small-step (reduction-stlye) semantics for Erlang, with and without rewrite rule tracing.
  - Build the Core Erlang Formalisation project (https://github.com/harp-project/Core-Erlang-Formalization/blob/master/README.md)
2. Build the the tester software with `make`

# Usage

- `make check`: executes the test suite
- `./scripts.erl <Erlang file/path>`: runs the Erlang code, and both semantics for the same code
- `./scripts.erl random <num>`: runs `<num>` random tests or stops after finding an error

In the `scripts.erl` file there are several options:

- With `TRACING` the coverage measurment can be turned on/off
- With `SHRINKING` the shrinking of found counterexamples can be turned on/off
- With `GHC_EXPORT` the extraction of the Core Erlang semantics can be turned on/off
- With `GEN_REC_LIMIT` the generated program size can be customized
- With `GEN_SIZE` the generated base value (e.g. variable names, numbers) sizes can be customized
- With `GEN_REC_WEIGHT` the propability of using recursive generation rule can be set
