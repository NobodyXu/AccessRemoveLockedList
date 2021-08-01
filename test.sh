#!/bin/sh -ex

export RUST_BACKTRACE=1

for feature in default permutation_testing; do
    cargo test --no-default-features --features $feature $@
    cargo test --release --no-default-features --features $feature $@
done
