#!/bin/sh

set -eu

"${CODEQL_DIST}/codeql" database index-files \
    --prune="**/*.testproj" \
    --include-extension=.js \
    --size-limit=5m \
    --language=lean \
    --working-dir=.\
    "$CODEQL_EXTRACTOR_LEAN_WIP_DATABASE"
