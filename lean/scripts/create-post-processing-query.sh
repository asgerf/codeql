#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

SCRIPT_DIR=$(dirname "$(realpath "$0")")
ROOT_DIR="$SCRIPT_DIR/.."

function strip_imports() {
    sed -E '/^ *(private )?import (codeql|All|MakeLanguageBase)/d'
}
function strip_signature() {
    sed -E 's/implements LanguageBaseSig<Location>//'
}

cat \
    "$ROOT_DIR"/ql/lib/codeql/js/base/*.qll \
    "$ROOT_DIR"/ql/lib/upgrades/post-process/PostProcess.ql \
    | strip_imports \
    | strip_signature
