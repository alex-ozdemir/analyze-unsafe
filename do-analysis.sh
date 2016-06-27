#!/bin/sh

# Set up the list of crates
filename=crate-list.txt
if [ ! -z "$1" ]; then filename=$1; fi

echo "crate target_type blocks functions methods impls declarations"

mkdir -p sources

for crate_name in $(cat $filename); do
    cd sources
    if [[ ! -a "$crate_name" ]]; then
        #>&2 echo "Cloning into $crate_name ... "
        eval cargo clone $crate_name 2> /dev/null > /dev/null
    fi
    if [[ -a $crate_name ]]; then
        cd "$crate_name"
        eval rustup run analyze cargo build
        # Remove the final binaryies. We don't use `clean` to avoid rebuilding deps.
        eval rustup run analyze cargo clean
        cd ..
    fi
    cd ..
done;

