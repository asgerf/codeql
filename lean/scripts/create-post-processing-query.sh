#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(dirname "$(realpath "$0")")
ROOT_DIR="$SCRIPT_DIR/.."

function strip_imports() {
    sed -E '/^(private )?import codeql/d'
}

cat \
    "$ROOT_DIR"/ql/lib/codeql/js/GeneratedAst.qll \
    "$ROOT_DIR"/ql/lib/codeql/js/PostProcessing.qll \
    "$ROOT_DIR"/ql/lib/upgrades/post-process/PostProcess.ql \
    | strip_imports
