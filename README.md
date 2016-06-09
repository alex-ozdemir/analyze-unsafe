# Analyze-Unsafe

Some of my work analyzing use of `unsafe` by crates on `crates.io`.

## Dependencies

All the rust is handled and build through `cargo`, which handles dependencies
:heart:, however, their are also some shell scripts which rely on `cargo-clone`
and `jq`.

### `cargo-clone`

This is an experimental cargo subcommand. Install is using `cargo install
cargo-clone`.

### `jq`

This is a command line tool for viewing and modifying JSON. It is available
[here](https://stedolan.github.io/jq/), and can also likely be installed using
a package manager. I installed it on Arch using Pacman, like so: `sudo pacman
-S jq`

## Write Up

As a work on the analysis, I intend to keep my (in progress)
[write-up](https://docs.google.com/document/d/1e6rsm8ML_7V-FvD8kOjVN7B2IhPopwtZjFM4iGavRdU/edit?usp=sharing)
and some
[data](https://docs.google.com/spreadsheets/d/13crG1zzeilrrM8Zcqtzw5WPiLuSkAMSFdzz7ANvhHKw/edit?usp=sharing)
online.
