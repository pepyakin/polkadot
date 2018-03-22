#!/bin/sh
set -e

cargo +nightly build --target=wasm32-unknown-unknown --release
for i in substrate_test_runtime
do
	# Add an export entry for the table defined in the module.
	wasm-export-table target/wasm32-unknown-unknown/release/$i.wasm target/wasm32-unknown-unknown/release/$i.export_table.wasm
	cp target/wasm32-unknown-unknown/release/$i.export_table.wasm target/wasm32-unknown-unknown/release/$i.wasm
	wasm-gc target/wasm32-unknown-unknown/release/$i.export_table.wasm target/wasm32-unknown-unknown/release/$i.compact.wasm
done
