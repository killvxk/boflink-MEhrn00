# MinGW MSVCRT Import Deduplication Example

This example demonstrates how boflink correctly deduplicates library imports when multiple object files reference the same functions from `msvcrt.dll`.

## Scenario

Multiple source files use common C runtime functions:
- `allocator.c` - Uses `malloc()` and `free()`
- `printer.c` - Uses `printf()`
- `main.c` - Uses `malloc()` (duplicate import test)

Even though `malloc` is used in two different files, boflink ensures it's only imported once from `msvcrt.dll`.

## Prerequisites

### Installing MinGW on macOS

```bash
# Install mingw-w64 using Homebrew
brew install mingw-w64
```

### Installing boflink

```bash
# Build and install boflink
cd /path/to/boflink
cargo xtask install
```

## Compiling

MinGW GCC (Linux/macOS):
```bash
./compile-mingw.sh
```

## Verifying Deduplication

After compilation, you can inspect the linked object to verify that each function (`malloc`, `free`, `printf`) appears only once in the import table:

```bash
objdump -t mingw-msvcrt-dedup.o | grep "__imp_"
```

You should see:
- `__imp_malloc` (once, not twice)
- `__imp_free` (once)
- `__imp_printf` (once)

## Expected Output

The example demonstrates that boflink's deduplication works correctly by ensuring "library_name + function_name" uniqueness across all object files.
