use std::collections::HashMap;

use crate::{
    linker::LinkerTargetArch,
    linkobject::import::{ImportMember, ImportName, ImportType},
};

/// MSVCRT CRT function symbol mappings for 64-bit
/// These are functions exported from msvcrt.dll (from dumpbin /exports)
/// Format: (symbol_in_obj_file, export_name_in_dll)
const MSVCRT64_SYMBOLS: &[(&str, &str)] = &[
    // Memory functions
    ("memset", "memset"),
    ("memcpy", "memcpy"),
    ("memmove", "memmove"),
    ("memcmp", "memcmp"),
    ("memchr", "memchr"),
    // String functions
    ("strlen", "strlen"),
    ("strcpy", "strcpy"),
    ("strncpy", "strncpy"),
    ("strcat", "strcat"),
    ("strncat", "strncat"),
    ("strcmp", "strcmp"),
    ("strncmp", "strncmp"),
    ("strchr", "strchr"),
    ("strrchr", "strrchr"),
    ("strstr", "strstr"),
    ("strspn", "strspn"),
    ("strcspn", "strcspn"),
    ("strpbrk", "strpbrk"),
    ("strtok", "strtok"),
    ("strnlen", "strnlen"),
    // Wide string functions
    ("wcslen", "wcslen"),
    ("wcscpy", "wcscpy"),
    ("wcsncpy", "wcsncpy"),
    ("wcscat", "wcscat"),
    ("wcsncat", "wcsncat"),
    ("wcscmp", "wcscmp"),
    ("wcsncmp", "wcsncmp"),
    ("wcschr", "wcschr"),
    ("wcsrchr", "wcsrchr"),
    ("wcsstr", "wcsstr"),
    ("wcsspn", "wcsspn"),
    ("wcscspn", "wcscspn"),
    ("wcspbrk", "wcspbrk"),
    ("wcstok", "wcstok"),
    ("wcsnlen", "wcsnlen"),
    // Printf/sprintf family
    ("printf", "printf"),
    ("sprintf", "sprintf"),
    ("snprintf", "_snprintf"),
    ("_snprintf", "_snprintf"),
    ("vprintf", "vprintf"),
    ("vsprintf", "vsprintf"),
    ("vsnprintf", "_vsnprintf"),
    ("_vsnprintf", "_vsnprintf"),
    // Printf_s variants
    ("printf_s", "printf_s"),
    ("sprintf_s", "sprintf_s"),
    ("vsprintf_s", "vsprintf_s"),
    // Wide printf
    ("wprintf", "wprintf"),
    ("swprintf", "swprintf"),
    ("wprintf_s", "wprintf_s"),
    // Scanf family
    ("scanf", "scanf"),
    ("sscanf", "sscanf"),
    ("scanf_s", "scanf_s"),
    // Math/utility
    ("abs", "abs"),
    // Memory allocation
    ("malloc", "malloc"),
    ("calloc", "calloc"),
    ("realloc", "realloc"),
    ("free", "free"),
    // Conversion functions
    ("atoi", "atoi"),
    ("atol", "atol"),
    ("strtol", "strtol"),
    ("strtoul", "strtoul"),
    ("strtod", "strtod"),
    ("wcstol", "wcstol"),
    ("wcstoul", "wcstoul"),
    ("wcstod", "wcstod"),
    // Character classification
    ("isalnum", "isalnum"),
    ("isalpha", "isalpha"),
    ("isdigit", "isdigit"),
    ("isspace", "isspace"),
    ("isupper", "isupper"),
    ("islower", "islower"),
    ("isprint", "isprint"),
    ("ispunct", "ispunct"),
    ("iscntrl", "iscntrl"),
    ("isxdigit", "isxdigit"),
    ("isgraph", "isgraph"),
    // Wide character classification
    ("iswalnum", "iswalnum"),
    ("iswalpha", "iswalpha"),
    ("iswdigit", "iswdigit"),
    ("iswspace", "iswspace"),
    ("iswupper", "iswupper"),
    ("iswlower", "iswlower"),
    ("iswprint", "iswprint"),
    ("iswpunct", "iswpunct"),
    ("iswcntrl", "iswcntrl"),
    ("iswxdigit", "iswxdigit"),
    ("iswgraph", "iswgraph"),
    // Character conversion
    ("tolower", "tolower"),
    ("toupper", "toupper"),
    ("towlower", "towlower"),
    ("towupper", "towupper"),
];

/// MSVCRT CRT function symbol mappings for 32-bit (with underscore prefix)
/// In 32-bit MSVC, C functions are decorated with underscore prefix
const MSVCRT32_SYMBOLS: &[(&str, &str)] = &[
    // Memory functions
    ("_memset", "memset"),
    ("_memcpy", "memcpy"),
    ("_memmove", "memmove"),
    ("_memcmp", "memcmp"),
    ("_memchr", "memchr"),
    // String functions
    ("_strlen", "strlen"),
    ("_strcpy", "strcpy"),
    ("_strncpy", "strncpy"),
    ("_strcat", "strcat"),
    ("_strncat", "strncat"),
    ("_strcmp", "strcmp"),
    ("_strncmp", "strncmp"),
    ("_strchr", "strchr"),
    ("_strrchr", "strrchr"),
    ("_strstr", "strstr"),
    ("_strspn", "strspn"),
    ("_strcspn", "strcspn"),
    ("_strpbrk", "strpbrk"),
    ("_strtok", "strtok"),
    ("_strnlen", "strnlen"),
    // Wide string functions
    ("_wcslen", "wcslen"),
    ("_wcscpy", "wcscpy"),
    ("_wcsncpy", "wcsncpy"),
    ("_wcscat", "wcscat"),
    ("_wcsncat", "wcsncat"),
    ("_wcscmp", "wcscmp"),
    ("_wcsncmp", "wcsncmp"),
    ("_wcschr", "wcschr"),
    ("_wcsrchr", "wcsrchr"),
    ("_wcsstr", "wcsstr"),
    ("_wcsspn", "wcsspn"),
    ("_wcscspn", "wcscspn"),
    ("_wcspbrk", "wcspbrk"),
    ("_wcstok", "wcstok"),
    ("_wcsnlen", "wcsnlen"),
    // Printf/sprintf family
    ("_printf", "printf"),
    ("_sprintf", "sprintf"),
    ("_snprintf", "_snprintf"),
    ("__snprintf", "_snprintf"),
    ("_vprintf", "vprintf"),
    ("_vsprintf", "vsprintf"),
    ("_vsnprintf", "_vsnprintf"),
    ("__vsnprintf", "_vsnprintf"),
    // Printf_s variants
    ("_printf_s", "printf_s"),
    ("_sprintf_s", "sprintf_s"),
    ("_vsprintf_s", "vsprintf_s"),
    // Wide printf
    ("_wprintf", "wprintf"),
    ("_swprintf", "swprintf"),
    ("_wprintf_s", "wprintf_s"),
    // Scanf family
    ("_scanf", "scanf"),
    ("_sscanf", "sscanf"),
    ("_scanf_s", "scanf_s"),
    // Math/utility
    ("_abs", "abs"),
    // Memory allocation
    ("_malloc", "malloc"),
    ("_calloc", "calloc"),
    ("_realloc", "realloc"),
    ("_free", "free"),
    // Conversion functions
    ("_atoi", "atoi"),
    ("_atol", "atol"),
    ("_strtol", "strtol"),
    ("_strtoul", "strtoul"),
    ("_strtod", "strtod"),
    ("_wcstol", "wcstol"),
    ("_wcstoul", "wcstoul"),
    ("_wcstod", "wcstod"),
    // Character classification
    ("_isalnum", "isalnum"),
    ("_isalpha", "isalpha"),
    ("_isdigit", "isdigit"),
    ("_isspace", "isspace"),
    ("_isupper", "isupper"),
    ("_islower", "islower"),
    ("_isprint", "isprint"),
    ("_ispunct", "ispunct"),
    ("_iscntrl", "iscntrl"),
    ("_isxdigit", "isxdigit"),
    ("_isgraph", "isgraph"),
    // Wide character classification
    ("_iswalnum", "iswalnum"),
    ("_iswalpha", "iswalpha"),
    ("_iswdigit", "iswdigit"),
    ("_iswspace", "iswspace"),
    ("_iswupper", "iswupper"),
    ("_iswlower", "iswlower"),
    ("_iswprint", "iswprint"),
    ("_iswpunct", "iswpunct"),
    ("_iswcntrl", "iswcntrl"),
    ("_iswxdigit", "iswxdigit"),
    ("_iswgraph", "iswgraph"),
    // Character conversion
    ("_tolower", "tolower"),
    ("_toupper", "toupper"),
    ("_towlower", "towlower"),
    ("_towupper", "towupper"),
];

/// Creates MSVCRT CRT symbol mappings for the specified architecture.
///
/// These symbols will be resolved as dynamic imports from msvcrt.dll,
/// using the Beacon loader's `__imp_MSVCRT$function` format.
///
/// The output symbol name format is `__imp_MSVCRT$function` which the Beacon
/// loader understands to resolve from msvcrt.dll at runtime.
pub fn symbols(architecture: LinkerTargetArch) -> HashMap<&'static str, ImportMember<'static>> {
    let symbol_names = if architecture == LinkerTargetArch::I386 {
        MSVCRT32_SYMBOLS
    } else {
        MSVCRT64_SYMBOLS
    };

    let mut symbol_map = HashMap::with_capacity(symbol_names.len() * 2);

    // Add the main symbol mappings (e.g., "_memset" -> __imp_MSVCRT$memset)
    // The symbol field is set to the desired output format for the Beacon loader
    symbol_map.extend(symbol_names.iter().map(|&(lookup_name, import_name)| {
        (
            lookup_name,
            ImportMember {
                architecture: architecture.into(),
                symbol: lookup_name, // Original symbol name, output name is computed later
                dll: "msvcrt",
                import: ImportName::Name(import_name),
                typ: ImportType::Code,
            },
        )
    }));

    // Also add __imp_ prefixed versions for dllimport declarations
    symbol_map.extend(symbol_names.iter().map(|&(lookup_name, import_name)| {
        let imp_lookup = format!("__imp_{}", lookup_name);

        // Leak the string to get a static lifetime
        let imp_lookup: &'static str = Box::leak(imp_lookup.into_boxed_str());

        (
            imp_lookup,
            ImportMember {
                architecture: architecture.into(),
                symbol: imp_lookup, // Original symbol name, output name is computed later
                dll: "msvcrt",
                import: ImportName::Name(import_name),
                typ: ImportType::Code,
            },
        )
    }));

    symbol_map
}
