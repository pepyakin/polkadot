#!/bin/bash

set -e

curdir=`dirname $0`

# Remove all .wasm artifacts (if any).
rm "$curdir/bin/*.wasm" &> /dev/null || true

# From files in ./src directory
# Take all .wat files
# And execute `wat2wasm` for each of them, putting
# results into ./bin directory.
for wat in $( ls -1 "$curdir/src" | grep '\.wat' ); do
	infile="$curdir/src/$wat"
	outfile="$curdir/bin/$( echo $wat | sed -e 's/\.wat$/\.wasm/g' )"

	echo "Compiling $infile -> $outfile"

	wat2wasm -o $outfile $infile
done
