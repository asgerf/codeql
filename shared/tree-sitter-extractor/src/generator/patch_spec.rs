use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Serialize, Deserialize, Debug)]
pub struct PatchSpec {
    /// Map from language name to language-specific patches
    pub languages: HashMap<String, LanguagePatch>,
}

impl PatchSpec {
    /// Get or insert a language patch for the specified language
    pub fn language_patch_mut(&mut self, language: &str) -> &mut LanguagePatch {
        self.languages
            .entry(language.to_string())
            .or_insert_with(LanguagePatch::default)
    }
}

/// Represents language-specific patches in the JSON document
#[derive(Serialize, Deserialize, Debug, Default, Clone)]
pub struct LanguagePatch {
    /// Maps node types to lists of synthetic node functions
    #[serde(rename = "syntheticNodes")]
    pub synthetic_nodes: HashMap<String, Vec<String>>,
    /// Maps node types to lists of base types
    #[serde(rename = "baseTypes")]
    pub base_types: HashMap<String, Vec<String>>,
}

impl LanguagePatch {
    /// Get or insert synthetic nodes for the specified node type
    pub fn synthetic_nodes_mut(&mut self, node_type: &str) -> &mut Vec<String> {
        self.synthetic_nodes
            .entry(node_type.to_string())
            .or_insert_with(Vec::new)
    }

    /// Get or insert base types for the specified node type
    pub fn base_types_mut(&mut self, node_type: &str) -> &mut Vec<String> {
        self.base_types
            .entry(node_type.to_string())
            .or_insert_with(Vec::new)
    }
}
