#!/bin/sh

set -eu

"${CODEQL_DIST}/codeql" database index-files \
    --prune="**/*.testproj" \
    --include-extension=.php \
    --size-limit=5m \
    --language=ql \
    --working-dir=.\
    "$CODEQL_EXTRACTOR_QL_WIP_DATABASE"
