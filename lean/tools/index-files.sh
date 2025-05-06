#!/bin/sh

set -eu

exec "${CODEQL_EXTRACTOR_LEAN_ROOT}/tools/${CODEQL_PLATFORM}/extractor" \
        extract \
        --file-list "$1" \
        --source-archive-dir "$CODEQL_EXTRACTOR_LEAN_SOURCE_ARCHIVE_DIR" \
        --output-dir "$CODEQL_EXTRACTOR_LEAN_TRAP_DIR"
