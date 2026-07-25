#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
WORK_DIR=${MEDDLY_VALIDATION_DIR:-"${TMPDIR:-/tmp}/meddly-evplus-validation"}
ARCHIVE="$WORK_DIR/meddly-0.18.1.tar.gz"
SOURCE_DIR="$WORK_DIR/meddly-0.18.1"
URL="https://downloads.sourceforge.net/project/meddly/meddly-0.18.1.tar.gz"
EXPECTED_SHA256="6a1bbcfa129a11d8426421cf5dc72aacac3672927ba404283495f785f6011ebf"
JOBS=${JOBS:-2}

for command in curl sha256sum tar make g++; do
    command -v "$command" >/dev/null || {
        echo "Missing required command: $command" >&2
        exit 2
    }
done

rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"

curl -fL --retry 3 -o "$ARCHIVE" "$URL"
echo "$EXPECTED_SHA256  $ARCHIVE" | sha256sum --check --strict

tar -xzf "$ARCHIVE" -C "$WORK_DIR"
cd "$SOURCE_DIR"

./configure --disable-shared --without-gmp
make -j"$JOBS"
make check

g++ -std=c++17 -O2 -I . -I src \
    "$SCRIPT_DIR/meddly_modsum_validation.cc" \
    src/.libs/libmeddly.a \
    -o "$WORK_DIR/meddly_modsum_validation"

"$WORK_DIR/meddly_modsum_validation"

echo
printf 'Validated MEDDLY 0.18.1 archive SHA-256: %s\n' "$EXPECTED_SHA256"
