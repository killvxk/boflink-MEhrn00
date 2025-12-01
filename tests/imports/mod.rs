use crate::link_yaml;
use boflink::linker::LinkerTargetArch;
use object::{Object, ObjectSymbol, coff::CoffFile};

#[test]
fn library_prefix() {
    let linked = link_yaml!("library_prefix.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    assert!(
        parsed
            .symbol_by_name("__imp_LIBRARY$imported_symbol")
            .is_some(),
        "Could not find symbol '__imp_LIBRARY$imported_symbol' in linked output"
    );
}

#[test]
fn import_thunks() {
    let linked = link_yaml!("import_thunks.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    let thunk_symbol = parsed
        .symbol_by_name("import")
        .expect("Could not find symbol 'import'");

    assert!(
        thunk_symbol.is_definition(),
        "thunk symbol should be defined"
    );

    let thunk_addr = thunk_symbol.coff_symbol().value.get(object::LittleEndian);

    let text_section = parsed
        .section_by_name(".text")
        .expect("Could not find .text section");

    let thunk_reloc = text_section
        .coff_relocations()
        .unwrap()
        .iter()
        .next()
        .expect(".text section should have a relocation");

    let reloc_addr = thunk_reloc.virtual_address.get(object::LittleEndian);

    assert_eq!(
        thunk_addr + 2,
        reloc_addr,
        "Thunk relocation address and thunk symbol address do not line up"
    );

    let reloc_target = parsed
        .symbol_by_index(thunk_reloc.symbol())
        .expect("Could not get thunk reloc target symbol");

    let target_name = reloc_target
        .name()
        .expect("Could not get thunk reloc target name");
    assert_eq!(
        target_name, "__imp_LIBRARY$import",
        "Thunk relocation target does not point to import symbol"
    );
}

#[test]
fn no_duplicate_imports() {
    let linked = link_yaml!("duplicate_imports.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // Count how many times the Sleep import symbol appears
    // Library imports are named as __imp_LIBRARY$symbol
    let sleep_symbols: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name == "__imp_KERNEL32$Sleep" && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        sleep_symbols.len(),
        1,
        "Expected exactly 1 Sleep import symbol, found {}",
        sleep_symbols.len()
    );
}

#[test]
fn multiple_symbols_same_library() {
    let linked = link_yaml!("multiple_symbols_same_lib.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // Verify both Sleep and CreateThread are imported from KERNEL32
    let sleep_import = parsed
        .symbol_by_name("__imp_KERNEL32$Sleep")
        .expect("Sleep import should exist");
    
    let create_thread_import = parsed
        .symbol_by_name("__imp_KERNEL32$CreateThread")
        .expect("CreateThread import should exist");

    assert!(
        !sleep_import.is_definition(),
        "Sleep import should not be a definition"
    );
    assert!(
        !create_thread_import.is_definition(),
        "CreateThread import should not be a definition"
    );
}

#[test]
fn multiple_objs_different_symbols_same_library() {
    let linked = link_yaml!("multiple_objs_different_symbols.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // obj1 imports Sleep, obj2 imports CreateThread
    // Both should be imported from KERNEL32, and each should appear exactly once
    
    let sleep_import = parsed
        .symbol_by_name("__imp_KERNEL32$Sleep")
        .expect("Sleep import should exist");
    
    let create_thread_import = parsed
        .symbol_by_name("__imp_KERNEL32$CreateThread")
        .expect("CreateThread import should exist");

    assert!(
        !sleep_import.is_definition(),
        "Sleep import should not be a definition"
    );
    assert!(
        !create_thread_import.is_definition(),
        "CreateThread import should not be a definition"
    );
    
    // Verify no duplicate imports by counting all KERNEL32 imports
    let kernel32_imports: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name.starts_with("__imp_KERNEL32$") && !s.is_definition()
            } else {
                false
            }
        })
        .collect();
    
    assert_eq!(
        kernel32_imports.len(),
        2,
        "Expected exactly 2 KERNEL32 imports (Sleep and CreateThread), found {}",
        kernel32_imports.len()
    );
}

#[test]
fn many_objs_same_import_stress_test() {
    let linked = link_yaml!("many_objs_same_import.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // 8 obj files all importing the same Sleep function
    // Should only result in ONE import symbol
    let sleep_symbols: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name == "__imp_KERNEL32$Sleep" && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        sleep_symbols.len(),
        1,
        "Expected exactly 1 Sleep import symbol even with 8 obj files, found {}",
        sleep_symbols.len()
    );
}

#[test]
fn mingw_msvcrt_multiple_imports() {
    let linked = link_yaml!("mingw_msvcrt_imports.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // Verify malloc is only imported once (obj1 and obj3 both use malloc)
    let malloc_symbols: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name == "__imp_msvcrt$malloc" && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        malloc_symbols.len(),
        1,
        "Expected exactly 1 malloc import from msvcrt, found {}",
        malloc_symbols.len()
    );

    // Verify free is imported once
    let free_symbols: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name == "__imp_msvcrt$free" && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        free_symbols.len(),
        1,
        "Expected exactly 1 free import from msvcrt, found {}",
        free_symbols.len()
    );

    // Verify printf is imported once
    let printf_symbols: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name == "__imp_msvcrt$printf" && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        printf_symbols.len(),
        1,
        "Expected exactly 1 printf import from msvcrt, found {}",
        printf_symbols.len()
    );

    // Verify total msvcrt imports count
    let all_msvcrt_imports: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name.starts_with("__imp_msvcrt$") && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        all_msvcrt_imports.len(),
        3,
        "Expected exactly 3 msvcrt imports (malloc, free, printf), found {}",
        all_msvcrt_imports.len()
    );
}

#[test]
fn ollvm_duplicate_imports() {
    // This test simulates OLLVM obfuscation where multiple different symbols 
    // (func_a, func_b) import the SAME function (Sleep) from the SAME library.
    // boflink should deduplicate the import entry but ensure both symbols are defined.
    let linked = link_yaml!("ollvm_duplicate_imports.yaml", LinkerTargetArch::Amd64);
    let parsed: CoffFile =
        CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    // Verify we have exactly ONE import for Sleep
    let sleep_imports: Vec<_> = parsed
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                name.contains("Sleep") && !s.is_definition()
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        sleep_imports.len(),
        1,
        "Expected exactly 1 Sleep import, found {}",
        sleep_imports.len()
    );
}
