#!/bin/sh
set -e

curdir=`dirname $0`

# Build wasm tests
cd "$curdir/wasm-tests"
./build.sh
cd - &>/dev/null


# Build wasm version of the runtime.
cd "$curdir/wasm"
./build.sh
cd - &>/dev/null
