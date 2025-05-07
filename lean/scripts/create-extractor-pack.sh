#!/bin/bash
set -eux

SCRIPT_DIR=$(dirname "$(realpath "$0")")

if [[ "$OSTYPE" == "linux-gnu"* ]]; then
  platform="linux64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
  platform="osx64"
else
  echo "Unknown OS"
  exit 1
fi

if which codeql >/dev/null; then
  CODEQL_BINARY="codeql"
elif gh codeql >/dev/null; then
  CODEQL_BINARY="gh codeql"
else
  gh extension install github/gh-codeql
  CODEQL_BINARY="gh codeql"
fi

cargo build --release
cargo run --release --bin codeql-extractor-lean -- generate --dbscheme ql/lib/lean.dbscheme --library ql/lib/codeql/js/base/GeneratedAst.qll
$CODEQL_BINARY query format -i ql/lib/codeql/js/base/GeneratedAst.qll

rm -rf extractor-pack
mkdir -p extractor-pack
cp -r codeql-extractor.yml tools ql/lib/lean.dbscheme ql/lib/lean.dbscheme.stats extractor-pack/

# Post-processing pack
cp -r ql/lib/upgrades/post-process extractor-pack/post-process

"$SCRIPT_DIR"/create-post-processing-query.sh > extractor-pack/post-process/PostProcess.ql

cp ql/lib/lean.dbscheme extractor-pack/post-process/lean.dbscheme
cp ql/lib/lean.dbscheme extractor-pack/post-process/old.dbscheme

mkdir -p extractor-pack/tools/${platform}
cp target/release/codeql-extractor-lean extractor-pack/tools/${platform}/extractor
