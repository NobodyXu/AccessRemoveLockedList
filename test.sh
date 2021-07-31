#!/bin/sh -ex

for feature in default permutation_testing; do
    cargo test --no-default-features --features $feature $@
    cargo test --release --no-default-features --features $feature $@
done
