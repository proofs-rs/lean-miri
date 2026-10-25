#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PINS="$ROOT/.pins"
STAGE="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-upstream.XXXXXXXX")"
trap 'rm -rf -- "$STAGE"' EXIT
mkdir -p "$PINS"

fetch_archive() {
  local file="$1" url="$2" expected_sha="$3" tmp_file
  if [[ ! -f "$file" ]]; then
    tmp_file="$STAGE/$(basename -- "$file").download"
    curl --fail --location --proto '=https' --tlsv1.2 --output "$tmp_file" "$url"
    mv -- "$tmp_file" "$file"
  fi
  if ! printf '%s  %s\n' "$expected_sha" "$file" | sha256sum --check --status; then
    printf 'SHA-256 mismatch for %s\n' "$file" >&2
    return 1
  fi
}

extract_full() {
  local name="$1" archive="$2" dest="$3" commit="$4" sentinel="$5" pin="$PINS/$1.commit" staged
  if [[ -d "$dest" ]]; then
    if [[ ! -f "$pin" || "$(cat -- "$pin")" != "$commit" || ! -f "$dest/$sentinel" ]]; then
      printf 'Existing extraction is not pinned as expected: %s\n' "$dest" >&2
      return 1
    fi
    return
  fi
  staged="$STAGE/$name"
  mkdir -p "$staged"
  tar --extract --gzip --file "$archive" --directory "$staged" --strip-components=1 --no-same-owner --no-same-permissions
  if [[ ! -f "$staged/$sentinel" ]]; then
    printf 'Expected source sentinel missing after extracting %s: %s\n' "$name" "$sentinel" >&2
    return 1
  fi
  mv -- "$staged" "$dest"
  printf '%s\n' "$commit" > "$pin"
}

extract_rustc_selection() {
  local archive="$1" dest="$2" commit="$3" paths="$4" pin="$PINS/rustc.commit" staged
  if [[ -d "$dest" ]]; then
    if [[ ! -f "$pin" || "$(cat -- "$pin")" != "$commit" || ! -f "$dest/compiler/rustc_const_eval/src/interpret/mod.rs" || ! -f "$dest/compiler/rustc_middle/src/ty/mod.rs" ]]; then
      printf 'Existing rustc extraction is not pinned as expected: %s\n' "$dest" >&2
      return 1
    fi
    # The selected path manifest can grow while keeping the same compiler pin.
    # Re-extract from the verified immutable archive so newly selected files are
    # present and existing selected files are restored byte-for-byte.
    tar --extract --gzip --file "$archive" --directory "$dest" --strip-components=1 --no-same-owner --no-same-permissions --files-from="$paths"
    return
  fi
  staged="$STAGE/rustc"
  mkdir -p "$staged"
  tar --extract --gzip --file "$archive" --directory "$staged" --strip-components=1 --no-same-owner --no-same-permissions --files-from="$paths"
  if [[ ! -f "$staged/compiler/rustc_const_eval/src/interpret/mod.rs" || ! -f "$staged/compiler/rustc_middle/src/ty/mod.rs" ]]; then
    printf 'Required rustc interpreter/type source missing after extraction\n' >&2
    return 1
  fi
  mv -- "$staged" "$dest"
  printf '%s\n' "$commit" > "$pin"
}

MIRI_COMMIT=7fa591d7d4dd9af8154becbc8332f8096f8323b1
RUSTC_COMMIT=8144389c895da997dbdecaa635e41d6a50be6ffd
APFLOAT_COMMIT=eeaacad81247af65d4043cb3e32d023a652d7951
APFLOAT_VERSION='0.2.3+llvm-462a31f5a5ab'

MIRI_ARCHIVE="$ROOT/miri-$MIRI_COMMIT.tar.gz"
RUSTC_ARCHIVE="$ROOT/rustc-$RUSTC_COMMIT.tar.gz"
APFLOAT_ARCHIVE="$ROOT/rustc_apfloat-$APFLOAT_VERSION.crate"

fetch_archive "$MIRI_ARCHIVE" "https://codeload.github.com/rust-lang/miri/tar.gz/$MIRI_COMMIT" 1360b191ff77f05a5746a5055f76fbce575dd012ad126d341d188326e6f8b074
fetch_archive "$RUSTC_ARCHIVE" "https://codeload.github.com/rust-lang/rust/tar.gz/$RUSTC_COMMIT" bf9feb74c700a8d1d71b318d4a2874d031af5d5380ff9151eb190330596a5aa2
fetch_archive "$APFLOAT_ARCHIVE" "https://static.crates.io/crates/rustc_apfloat/rustc_apfloat-$APFLOAT_VERSION.crate" 486c2179b4796f65bfe2ee33679acf0927ac83ecf583ad6c91c3b4570911b9ad

extract_full miri "$MIRI_ARCHIVE" "$ROOT/miri-source" "$MIRI_COMMIT" rust-version
extract_rustc_selection "$RUSTC_ARCHIVE" "$ROOT/rustc-source" "$RUSTC_COMMIT" "$ROOT/rustc-selected-files.txt"
extract_full rustc_apfloat "$APFLOAT_ARCHIVE" "$ROOT/rustc-apfloat-source" "$APFLOAT_COMMIT" src/lib.rs

# Runtime AES hazmat source, exact package selected by Miri Cargo.lock.
AES_COMMIT=c1534361e7549e29a16c3505f45a04c92d26b62a
AES_ARCHIVE="$ROOT/aes-0.9.3.crate"
fetch_archive "$AES_ARCHIVE" "https://static.crates.io/crates/aes/aes-0.9.3.crate" 35f0f96ce78e38c3dc6d8948aa8163d06385be74000f3c7a95bf1eef35d3ea32
mkdir -p "$ROOT/crates"
extract_full aes "$AES_ARCHIVE" "$ROOT/crates/aes-0.9.3" "$AES_COMMIT" src/hazmat.rs

if [[ "$(tr -d '\r\n' < "$ROOT/miri-source/rust-version")" != "$RUSTC_COMMIT" ]]; then
  printf 'Miri rust-version does not match the pinned rustc commit\n' >&2
  exit 1
fi
printf 'Pinned Miri, selected rustc, and rustc_apfloat sources are present and archive hashes match.\n'
