#!/bin/bash

export LOOM_CHECKPOINT_FILE=loom.json
export LOOM_CHECKPOINT_INTERVAL=1
export LOOM_LOG=1
export LOOM_LOCATION=1

feature="permutation_testing"

if [ $# -lt 1 ]; then
    echo "Usage: $0 <test name> [args to cargo test]" >&2
    exit 1
fi

cd $(dirname $(realpath $0))
exec cargo test \
    --target-dir target-"$feature" \
    --release \
    --no-default-features \
    --features "$feature" \
    $1 \
    ${@:2}
