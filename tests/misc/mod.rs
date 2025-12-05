use boflink::linker::LinkerTargetArch;
use object::{
    Object,
    coff::CoffFile,
    pe::{
        IMAGE_SCN_CNT_CODE, IMAGE_SCN_CNT_INITIALIZED_DATA, IMAGE_SCN_MEM_EXECUTE,
        IMAGE_SCN_MEM_READ, IMAGE_SCN_MEM_WRITE,
    },
};

use crate::setup_linker;

#[test]
fn externals_relaxation() {
    // The entrypoint will be added as an undefined external. Since there will
    // be no references and the symbol is undefined, the BOF should link
    let _ = setup_linker!("externals_relaxation.yaml", LinkerTargetArch::Amd64)
        .entrypoint("go")
        .build()
        .link()
        .expect("Could not link files");
}

#[test]
fn no_merge_groups() {
    let linked = setup_linker!("no_merge_groups.yaml", LinkerTargetArch::Amd64)
        .merge_grouped_sections(false)
        .build()
        .link()
        .expect("Could not link inputs");

    let coff: CoffFile = CoffFile::parse(linked.as_slice()).expect("Could not parse linked output");

    let test_sections: &[(&str, u32)] = &[
        (
            ".text$a",
            IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ,
        ),
        (
            ".text$b",
            IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ,
        ),
        (
            ".text$c",
            IMAGE_SCN_CNT_CODE | IMAGE_SCN_MEM_EXECUTE | IMAGE_SCN_MEM_READ,
        ),
        (
            ".data$a",
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE,
        ),
        (
            ".data$b",
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE,
        ),
        (
            ".data$c",
            IMAGE_SCN_CNT_INITIALIZED_DATA | IMAGE_SCN_MEM_READ | IMAGE_SCN_MEM_WRITE,
        ),
    ];

    for &(test_name, test_characteristics) in test_sections {
        let section = coff
            .section_by_name(test_name)
            .unwrap_or_else(|| panic!("Could not find section {test_name}"));

        let characteristics = section
            .coff_section()
            .characteristics
            .get(object::LittleEndian);

        assert!(
            characteristics & test_characteristics == test_characteristics,
            "{test_name} section has invalid characteristics. characteristics = {characteristics:#x?}, test_characteristics = {test_characteristics:#x?}, contained = {:#x?}",
            characteristics & test_characteristics
        );
    }
}

#[test]
fn symbol_cleanup() {
    use object::{ObjectSection, ObjectSymbol};
    
    let linked = setup_linker!("symbol_cleanup.yaml", LinkerTargetArch::Amd64)
        .build()
        .link()
        .expect("Could not link files");
        
    let coff: CoffFile = CoffFile::parse(linked.as_slice()).expect("Could not parse linked COFF");

    // Verify go (important symbol) is preserved
    assert!(
        coff.symbol_by_name("go").is_some(),
        "go symbol should be preserved as it is important"
    );

    // Verify used_function (referenced) is preserved
    assert!(
        coff.symbol_by_name("used_function").is_some(),
        "used_function symbol should be preserved as it is referenced"
    );

    // Verify unused_function (unreferenced, not important) is removed
    assert!(
        coff.symbol_by_name("unused_function").is_none(),
        "unused_function symbol should be removed as it is unreferenced"
    );

    // Verify unused_global_var (unreferenced COMMON symbol) is removed
    assert!(
        coff.symbol_by_name("unused_global_var").is_none(),
        "unused_global_var COMMON symbol should be removed as it is unreferenced"
    );

    // Count global symbols - should only have go and used_function
    let global_symbol_count = coff
        .symbols()
        .filter(|s| s.is_global())
        .count();

    assert_eq!(
        global_symbol_count, 2,
        "Should have exactly 2 global symbols (go and used_function), found {global_symbol_count}"
    );
}

#[test]
fn symbol_deduplication() {
    use object::ObjectSymbol;
    
    // Link 3 objects:
    // 1. Defines global "duplicate" 
    // 2. Defines global "duplicate" (duplicate definition)
    // 3. Defines entrypoint "go" that references "duplicate"
    //
    // With deduplicate_symbols enabled:
    // - Duplicate symbol error is suppressed
    // - First "duplicate" keeps original name
    // - Second "duplicate" is renamed to "duplicat1"
    let linked = setup_linker!("symbol_dedup.yaml", LinkerTargetArch::Amd64)
        .deduplicate_symbols(true)
        .gc_sections(false)
        .build()
        .link()
        .expect("Could not link files");
        
    let coff: CoffFile = CoffFile::parse(linked.as_slice()).expect("Could not parse linked COFF");

    // "go" is the entrypoint - should be preserved as-is
    assert!(
        coff.symbol_by_name("go").is_some(),
        "Entrypoint 'go' should be preserved"
    );

    // First occurrence of "duplicate" should keep original name
    let duplicate_original = coff.symbol_by_name("duplicate");
    assert!(
        duplicate_original.is_some(),
        "First 'duplicate' symbol should keep original name"
    );

    // Second occurrence should be renamed to "duplicat1"
    let renamed_symbols: Vec<_> = coff
        .symbols()
        .filter(|s| {
            if let Ok(name) = s.name() {
                // Check for renamed symbol: starts with "duplicat" (prefix) and ends with digit
                name.starts_with("duplicat") && name.len() == 9 && name != "duplicate"
            } else {
                false
            }
        })
        .collect();

    assert_eq!(
        renamed_symbols.len(),
        1,
        "Expected 1 renamed duplicate symbol (e.g. 'duplicat1'), found {}",
        renamed_symbols.len()
    );

    // Verify renamed symbol has same length as original
    if let Some(renamed) = renamed_symbols.first() {
        let renamed_name = renamed.name().expect("Could not get renamed symbol name");
        assert_eq!(
            renamed_name.len(),
            "duplicate".len(),
            "Renamed symbol '{}' should have same length as 'duplicate'",
            renamed_name
        );
    }
}
