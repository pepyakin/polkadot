#!/bin/sh

curdir=`dirname $0`

function build {
	project_root=$1
	echo "Building $project_root"
	cd $project_root
	./build.sh
	cd - &>/dev/null
}

build "$curdir/substrate/executor/wasm"
build "$curdir/substrate/test-runtime/wasm"
build "$curdir/polkadot/runtime/wasm"
build "$curdir/demo/runtime"
