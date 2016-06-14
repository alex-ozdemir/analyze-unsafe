#!/bin/zsh
script_dir=${0%/*}
path_to_bin="$script_dir/../../target/debug/analyze"
for line in $(cargo read-manifest |
    jq '{name: .name, target: .targets | .[] | select(.kind != ["test"]) | {name: .name, src_path: .src_path, kind: .kind| .[0]}}' |
    jq '.name + " " + .target.name + " " + .target.kind + " " + .target.src_path' |
    sed -e 's/^"//g' -e 's/"$//g' -e 's/ /,/g'); do
    array=(${(s/,/)line})
    crate=$array[1]
    target=$array[2]
    ty=$array[3]
    src=$array[4]
    eval $path_to_bin -Z keep_ast --sysroot $HOME/.multirust/toolchains/nightly $src --extern libc=/home/aozdemir/learning/pgm-analysis/analyze-unsafe/sources/libctest/target/debug/deps/liblibc-6b483f9a7097e9a4.rlib
    # eval $path_to_bin $crate $target $ty -Z keep_ast --sysroot $HOME/.multirust/toolchains/nightly $src --extern libc=/home/aozdemir/learning/pgm-analysis/analyze-unsafe/sources/libctest/target/debug/deps/liblibc-6b483f9a7097e9a4.rlib
done;
