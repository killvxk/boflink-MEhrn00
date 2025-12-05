# Symbol Deduplication Example

This example demonstrates the `--deduplicate-symbols` feature in boflink.

## Problem

When linking multiple object files, you may have multiple static (local) functions
with the same name. While this isn't an error (static functions have internal linkage),
some tools require unique symbol names in the final output.

With `--deduplicate-symbols`, boflink renames duplicate symbol names while preserving
their length, ensuring uniqueness in the symbol table.

## Files

- `module1.c` - Defines a static function `get_counter()` 
- `module2.c` - Also defines a static function `get_counter()` (same name!)
- `go.c` - Entry point that calls both modules

## How it works

Without `--deduplicate-symbols`:
```
boflink -o output.o module1.o module2.o go.o
# Both 'get_counter' symbols exist with the same name
```

With `--deduplicate-symbols`:
```
boflink --deduplicate-symbols -o output.o module1.o module2.o go.o
# First 'get_counter' keeps name, second becomes 'get_count01' (same length = 6 chars)
```

## Building

### Using MinGW (Linux/macOS)
```bash
./compile-mingw.sh
```

### Using Clang
```bash
./compile-clang.sh
```

## Verifying

After building, inspect the symbol table:
```bash
llvm-nm output.o | grep -E "get_counter|process"
# Should show: get_counter, get_counte0, process_module1, process_module2
```

Or use objdump:
```bash
llvm-objdump -t output.o | grep get_counter
```
