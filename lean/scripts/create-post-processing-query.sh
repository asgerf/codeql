#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(dirname "$(realpath "$0")")
ROOT_DIR="$SCRIPT_DIR/.."

function rewrite_imports() {
    while read -r line; do
        if [[ $line =~ ^[[:space:]]*(private[[:space:]]+)?import[[:space:]]+ ]]; then
            # Replace dots with underscores in import statements
            echo "$line" | sed -E 's/\./_/g'
        else
            # Pass through other lines unchanged
            echo "$line"
        fi
    done
}

function wrap_file() {
    Prefix="$1"
    FileWithoutExtension=$(basename "$2" | sed 's/\.[^.]*$//')
    ModuleName="${Prefix}${FileWithoutExtension}"

    echo "module $ModuleName {"
    rewrite_imports < "$2"
    echo "}"
}

wrap_file codeql_shared_ "$ROOT_DIR"/ql/lib/codeql/shared/LanguageBase.qll
for file in "$ROOT_DIR"/ql/lib/codeql/js/base/*.qll; do
    wrap_file codeql_js_base_ "$file"
done
for file in "$ROOT_DIR"/ql/lib/upgrades/post-process/*.qll; do
    wrap_file "" "$file"
done
wrap_file "" "$ROOT_DIR"/ql/lib/upgrades/post-process/PostProcess.ql

echo
echo "module All = codeql_js_base_All;" # Allow 'import All' without full prefix
echo "module FacadeAst = codeql_js_base_FacadeAst;" # GeneratedAst imports this
echo
echo "import PostProcess::QueryPredicates"
echo
