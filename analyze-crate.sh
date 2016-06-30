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
        rustup run analyze cargo build --verbose > "../../output/$crate_name.out" 2>&1
        # Remove the final binaryies. We don't use `clean` to avoid rebuilding deps.
        rustup run analyze cargo clean --verbose >> "../../output/$crate_name.out" 2>&1
        cd ..
    fi
    cd ..
}

assert_nz() {
    if [ -z "$1" ]; then err "assert_nz $2"; fi
}

main "$@"
