use std::collections::HashMap;

/// Helper for generating unique symbol names while preserving length.
#[derive(Debug)]
pub struct SymbolNameDeduplicator {
    seen_names: HashMap<String, usize>,
}

impl SymbolNameDeduplicator {
    pub fn new() -> Self {
        Self {
            seen_names: HashMap::new(),
        }
    }

    /// Checks if a name has been seen before and generates a unique variant if needed.
    /// Returns (original_or_renamed, is_first_occurrence).
    pub fn deduplicate(&mut self, name: &str) -> (String, bool) {
        let count = self.seen_names.entry(name.to_string()).or_insert(0);
        *count += 1;

        if *count == 1 {
            // First occurrence, keep original name
            (name.to_string(), true)
        } else {
            // Generate unique name with same length
            let renamed = Self::generate_unique_name(name, *count - 1);
            (renamed, false)
        }
    }

    /// Generates a unique name by replacing suffix with counter.
    /// Ensures the output has exactly the same length as the input.
    fn generate_unique_name(original: &str, counter: usize) -> String {
        let len = original.len();
        
        if len == 0 {
            return original.to_string();
        }

        // Convert counter to string
        let counter_str = counter.to_string();
        
        if counter_str.len() >= len {
            // Name is too short for decimal counter, use base36
            return Self::format_base36(counter, len);
        }

        // Replace last N characters with counter
        let prefix_len = len - counter_str.len();
        let prefix = &original[..prefix_len];
        
        format!("{}{}", prefix, counter_str)
    }

    /// Formats a number in base36 (0-9, a-z) with exact length.
    fn format_base36(mut num: usize, width: usize) -> String {
        const DIGITS: &[u8] = b"0123456789abcdefghijklmnopqrstuvwxyz";
        
        if width == 0 {
            return String::new();
        }

        let mut result = Vec::with_capacity(width);
        
        // Generate base36 digits (least significant first)
        for _ in 0..width {
            result.push(DIGITS[num % 36]);
            num /= 36;
        }

        // Reverse to get most significant first
        result.reverse();
        
        // All characters are ASCII digits/letters, so this cannot fail
        String::from_utf8(result).expect("base36 encoding should always be valid UTF-8")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_occurrence() {
        let mut dedup = SymbolNameDeduplicator::new();
        let (name, is_first) = dedup.deduplicate("symbol");
        assert_eq!(name, "symbol");
        assert!(is_first);
    }

    #[test]
    fn test_second_occurrence() {
        let mut dedup = SymbolNameDeduplicator::new();
        dedup.deduplicate("func");
        let (name, is_first) = dedup.deduplicate("func");
        assert_eq!(name, "fun1");
        assert_eq!(name.len(), 4); // Same length as "func"
        assert!(!is_first);
    }

    #[test]
    fn test_multiple_occurrences() {
        let mut dedup = SymbolNameDeduplicator::new();
        dedup.deduplicate("test");
        dedup.deduplicate("test");
        let (name3, _) = dedup.deduplicate("test");
        assert_eq!(name3, "tes2");
        assert_eq!(name3.len(), 4);
    }

    #[test]
    fn test_different_names() {
        let mut dedup = SymbolNameDeduplicator::new();
        dedup.deduplicate("foo");
        let (name, is_first) = dedup.deduplicate("bar");
        assert_eq!(name, "bar");
        assert!(is_first);
    }

    #[test]
    fn test_short_name() {
        let mut dedup = SymbolNameDeduplicator::new();
        dedup.deduplicate("a");
        let (name, _) = dedup.deduplicate("a");
        // Should use base36 for very short names
        assert_eq!(name.len(), 1);
    }

    #[test]
    fn test_base36() {
        assert_eq!(SymbolNameDeduplicator::format_base36(0, 3), "000");
        assert_eq!(SymbolNameDeduplicator::format_base36(1, 3), "001");
        assert_eq!(SymbolNameDeduplicator::format_base36(35, 3), "00z");
        assert_eq!(SymbolNameDeduplicator::format_base36(36, 3), "010");
    }
}
