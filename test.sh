#!/bin/bash -ex

args="--no-default-features"

run_test() {
    cargo test $args --target-dir target-"$1" --features "$1" ${@:2}
}

run_miri() {
    cargo +nightly miri test $args --target-dir miri-target-"$1" --features "$1" ${@:2}
}

main() {
    export RUST_BACKTRACE=1
    # Allow environment variables to pass through
    export MIRIFLAGS="-Zmiri-disable-isolation"
    export LANG=C.UTF8

    run_test default $@
    run_test default --release $@

    run_test permutation_testing --release $@

    run_miri default $@
    run_miri default ---release $@
}

if [ -z ${CLEARED+x} ]; then
    exec env -i \
        CLEARED=1 \
        TERM="$TERM" \
        PATH="$PATH" \
        RUSTUP_HOME="$RUSTUP_HOME" \
        CARGO_HOME="$CARGO_HOME" \
        $0 $@
else
    cd $(dirname $(realpath $0))
    main $@
fi
