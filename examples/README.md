# Examples

This directory contains example BOF (Beacon Object File) projects demonstrating how to use boflink.

## Available Examples

| Example | Description |
|---------|-------------|
| [basic](basic/) | Single source file compilation and linking |
| [custom-api](custom-api/) | Using a custom API instead of Beacon API |
| [mingw-msvcrt-dedup](mingw-msvcrt-dedup/) | MinGW MSVCRT symbol deduplication |
| [mingw-standalone](mingw-standalone/) | Standalone MinGW compilation |
| [multiple-sources](multiple-sources/) | Multiple source file linking |
| [symbol-dedup](symbol-dedup/) | Symbol deduplication feature |

## Compiling with MSVC

### Prerequisites

- Visual Studio 2022 (or compatible version)
- Windows SDK

### Step 1: Compile with cl.exe

Open a Developer Command Prompt or run vcvars64.bat first:

```cmd
call "C:\Program Files\Microsoft Visual Studio\2022\Enterprise\VC\Auxiliary\Build\vcvars64.bat"
```

Then compile:

```cmd
cl /GS- /c /Fo:output.obj source.c
```

Key flags:
- `/GS-` - Disable buffer security check (required for BOF)
- `/c` - Compile only, do not link

### Step 2: Link with boflink

```cmd
boflink -o output.bof output.obj -lkernel32 -ladvapi32 ^
  -L "C:\Program Files (x86)\Windows Kits\10\Lib\10.0.26100.0\um\x64" ^
  -L "C:\Program Files\Microsoft Visual Studio\2022\Enterprise\VC\Tools\MSVC\14.44.35207\lib\x64"
```

Key options:
- `-o` - Output file name
- `-l` - Link with import library
- `-L` - Add library search path

### Library Search Paths

You need to provide paths to:

1. **Windows SDK** (`um\x64`): Contains kernel32.lib, advapi32.lib, etc.
   ```
   C:\Program Files (x86)\Windows Kits\10\Lib\<version>\um\x64
   ```

2. **MSVC CRT** (optional): Contains libcmt.lib, oldnames.lib
   ```
   C:\Program Files\Microsoft Visual Studio\2022\<edition>\VC\Tools\MSVC\<version>\lib\x64
   ```

### Example: basic

```cmd
cd examples\basic

:: Compile
cl /GS- /c /Fo:basic.obj basic.c

:: Link
boflink -o basic.bof basic.obj -lkernel32 -ladvapi32 ^
  -L "C:\Program Files (x86)\Windows Kits\10\Lib\10.0.26100.0\um\x64" ^
  -L "C:\Program Files\Microsoft Visual Studio\2022\Enterprise\VC\Tools\MSVC\14.44.35207\lib\x64"
```

### Example: multiple-sources

```cmd
cd examples\multiple-sources

:: Compile
cl /GS- /c /Fo:go.obj go.c
cl /GS- /c /Fo:other.obj other.c

:: Link
boflink -o multiple.bof go.obj other.obj ^
  -L "C:\Program Files (x86)\Windows Kits\10\Lib\10.0.26100.0\um\x64" ^
  -L "C:\Program Files\Microsoft Visual Studio\2022\Enterprise\VC\Tools\MSVC\14.44.35207\lib\x64"
```

## Compiling with MinGW

See individual example README files for MinGW compilation instructions.

## Verifying Output

You can verify the generated BOF file using the `file` command:

```bash
file basic.bof
# Output: x86-64 COFF object file, no line number info, not stripped, 5 sections, ...
```

Or use `objdump` to inspect symbols:

```bash
objdump -t basic.bof
```
