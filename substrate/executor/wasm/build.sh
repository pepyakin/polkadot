#!/bin/sh
set -e

cargo +nightly build --target=wasm32-unknown-unknown --release
for i in test
do
	# Add an export entry for the table defined in the module.
	wasm-export-table target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.export_table.wasm
	cp target/wasm32-unknown-unknown/release/runtime_$i.export_table.wasm target/wasm32-unknown-unknown/release/runtime_$i.wasm
	wasm-gc target/wasm32-unknown-unknown/release/runtime_$i.export_table.wasm target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm
done
