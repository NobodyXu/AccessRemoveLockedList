#!/bin/sh -ex

cd $(dirname $(realpath $0))

export RUST_BACKTRACE=1
# Allow environment variables to pass through
export MIRIFLAGS="-Zmiri-disable-isolation"

args="--no-default-features"
miri_args="$args --target-dir miri-target"

for feature in default; do
    cargo +nightly miri test $miri_args --features $feature $@
    cargo +nightly miri test --release $miri_args --features $feature $@
done

feature="permutation_testing"
cargo test $args --features $feature $@
cargo test --release $args --features $feature $@
