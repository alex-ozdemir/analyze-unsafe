#!/bin/sh

main () {
    crate_name="$1"
    assert_nz "$crate_name"
    cd sources
    if [[ ! -a "$crate_name" ]]; then
        eval cargo clone $crate_name > /dev/null
    fi
    if [[ -a $crate_name ]]; then
        cd "$crate_name"
        eval rustup run analyze cargo build --verbose 2>&1 > "../../output/$crate_name.out"
        # Remove the final binaryies. We don't use `clean` to avoid rebuilding deps.
        eval rustup run analyze cargo clean --verbose 2>&1 >> "../../output/$crate_name.out"
        cd ..
    fi
    cd ..
}

assert_nz() {
    if [ -z "$1" ]; then err "assert_nz $2"; fi
}

main "$@"
