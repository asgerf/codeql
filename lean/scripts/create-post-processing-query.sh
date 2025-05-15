#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(dirname "$(realpath "$0")")
ROOT_DIR="$SCRIPT_DIR/.."

function strip_imports() {
    sed -E '/^ *(private )?import (codeql|MakeLanguageBase)/d'
}
function strip_signature() {
    sed -E 's/implements LanguageBaseSig<Location>//'
}

function wrap_file() {
    ModuleName=$(basename "$1" .ql)
    echo "module $ModuleName {"
    cat "$1"
    echo "}"
}

{
    for file in "$ROOT_DIR"/ql/lib/codeql/js/base/*.qll; do
        wrap_file "$file"
    done
    cat "$ROOT_DIR"/ql/lib/upgrades/post-process/PostProcess.ql
} | strip_imports | strip_signature
