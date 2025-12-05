#!/bin/sh
# Compile using MinGW GCC with boflink
# Assumes that the program was installed using `cargo xtask install`.

libexec="$HOME/.local/libexec/boflink"

# Step 1: Compile source files to object files
echo "Compiling source files..."
x86_64-w64-mingw32-gcc -c allocator.c -o allocator.o
x86_64-w64-mingw32-gcc -c printer.c -o printer.o
x86_64-w64-mingw32-gcc -c main.c -o main.o

# Step 2: Link using boflink
echo "Linking with boflink..."
~/.cargo/bin/boflink --mingw64 -lmsvcrt -o mingw-msvcrt-dedup.o allocator.o printer.o main.o

echo ""
echo "Verifying import deduplication..."
echo "Checking for __imp_ symbols:"
objdump -t mingw-msvcrt-dedup.o | grep "__imp_" | sort

echo ""
echo "Expected output:"
echo "- ONE __imp_malloc entry (not two, even though used in allocator.c and main.c)"
echo "- ONE __imp_free entry"
echo "- msvcrt imports (snprintf, etc.)"
