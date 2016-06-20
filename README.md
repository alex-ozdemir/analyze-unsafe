# Analyze-Unsafe

Some of my work analyzing use of `unsafe` by crates on `crates.io`.

## Runbook

Right now the repository is set up to run a backwards dataflow analysis to see
if dereferenced pointers originate in public interfaces.

To see it in action, check out `examples/v1.rs` and run `cargo run --bin
analyze -- --sysroot ~/.multirust/toolchains/nightly-x86_64-unknown-linux-gnu
examples/v1.rs`, where you will need to replace `~/.multirust/toolchains/nightly-x86_64-unknown-linux-gnu` with the location of your nightly install.

## Write Up

As a work on the analysis, I intend to keep my (in progress)
[write-up](https://docs.google.com/document/d/1e6rsm8ML_7V-FvD8kOjVN7B2IhPopwtZjFM4iGavRdU/edit?usp=sharing)
and some
[data](https://docs.google.com/spreadsheets/d/13crG1zzeilrrM8Zcqtzw5WPiLuSkAMSFdzz7ANvhHKw/edit?usp=sharing)
online.
