#!/bin/bash
# Compile and link with symbol deduplication using MinGW

set -e

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BOFLINK_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

echo "=== Compiling object files (32-bit) ==="
i686-w64-mingw32-gcc -c -fdata-sections -o module1.o module1.c
i686-w64-mingw32-gcc -c -fdata-sections -o module2.o module2.c  
i686-w64-mingw32-gcc -c -o go.o go.c

echo ""
echo "=== Linking with --deduplicate-symbols ==="
cargo run --manifest-path "$BOFLINK_ROOT/Cargo.toml" -- \
    --deduplicate-symbols \
    -o output.o \
    module1.o module2.o go.o

cargo run --manifest-path "$BOFLINK_ROOT/Cargo.toml" -- \
    -o output1.o \
    module1.o module2.o go.o

echo ""
echo "=== Symbol table (showing helper functions) ==="
if command -v llvm-nm &> /dev/null; then
    llvm-nm output.o | grep -E "(helper|process_)" || true
elif command -v nm &> /dev/null; then
    nm output.o | grep -E "(helper|process_)" || true
else
    echo "No nm tool found, skipping symbol dump"
fi

echo ""
echo "=== Done! Check output.o ==="
