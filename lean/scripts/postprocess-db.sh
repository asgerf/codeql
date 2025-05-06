#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

set -x

# Get own directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$SCRIPT_DIR/.."
SHARED_DIR="$ROOT_DIR/../shared"

# Get the database path
DB_PATH="${1:-}"
if [[ -z "$DB_PATH" ]]; then
    echo "Usage: $0 <path-to-database>"
    exit 1
fi

DATASET_PATH="$DB_PATH/db-lean"

if ! [[ -f "$DATASET_PATH/lean.dbscheme" ]]; then
    echo "Error: $DB_PATH/lean.dbscheme does not exist. Does not seem to be a valid database."
    exit 1
fi

# Get a temporary directory
TEMP_DIR=$(mktemp -d)

# Save the original dbscheme
cp "$DATASET_PATH/lean.dbscheme" "$TEMP_DIR/lean.dbscheme"

# Generate a dummy dbscheme
cp "$DATASET_PATH/lean.dbscheme" "$TEMP_DIR/dummy.dbscheme"
printf "\n// dummy change\n" >> "$TEMP_DIR/dummy.dbscheme"
OldHash=$(git hash-object "$TEMP_DIR/dummy.dbscheme")

GeneratedUpgradeDir="$TEMP_DIR/upgrades/$OldHash"
mkdir -p "$GeneratedUpgradeDir"

cp -r "$ROOT_DIR/ql/lib/upgrades/postprocess/" "$TEMP_DIR/upgrades/$OldHash/"
cp "$TEMP_DIR/dummy.dbscheme" "$TEMP_DIR/upgrades/$OldHash/old.dbscheme"
cp "$TEMP_DIR/lean.dbscheme" "$TEMP_DIR/upgrades/$OldHash/lean.dbscheme"

# Copy dependencies into the upgrade directory since upgrade scripts can't import outside files
mkdir -p "$GeneratedUpgradeDir/codeql"
cp "$ROOT_DIR/ql/lib/codeql/Locations.qll" "$GeneratedUpgradeDir/codeql/"
cp -r "$ROOT_DIR/ql/lib/files/" "$GeneratedUpgradeDir/files"

mkdir -p "$GeneratedUpgradeDir/codeql/util"
cp "$SHARED_DIR/util/codeql/util/FileSystem.qll" "$GeneratedUpgradeDir/codeql/util"

# Generate the qlpack.yml file
cat > "$TEMP_DIR/qlpack.yml" << EOF
name: codeql/synthesize
version: 0.0.1
dbscheme: lean.dbscheme
upgrades: upgrades
EOF

echo "Generated upgrade pack in: $GeneratedUpgradeDir"
echo "About to mutate database"
read -r

# Insert the dummy dbscheme into the target database so we can upgrade back to the real one
cp "$TEMP_DIR/dummy.dbscheme" "$DATASET_PATH/lean.dbscheme"

# Run the upgrade
codeql database upgrade --target-dbscheme="$TEMP_DIR/upgrades/$OldHash/lean.dbscheme" --search-path="$TEMP_DIR" -- "$DB_PATH"
