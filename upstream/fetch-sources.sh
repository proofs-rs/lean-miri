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

# Exact selected layout-randomization dependencies from pinned rustc Cargo.lock.
fetch_selected_crate() {
  local component="$1" name="$2" version="$3" digest="$4" commit="$5"
  shift 5
  local archive="$ROOT/$name-$version.crate" file
  local selected=()
  fetch_archive "$archive" "https://static.crates.io/crates/$name/$name-$version.crate" "$digest"
  for file in "$@"; do selected+=("$name-$version/$file"); done
  mkdir -p "$ROOT/crates/$name-$version"
  tar --extract --gzip --file "$archive" --directory "$ROOT/crates/$name-$version" \
    --strip-components=1 --no-same-owner --no-same-permissions "${selected[@]}"
  printf '%s\n' "$commit" > "$PINS/$component.commit"
}

fetch_selected_crate rustc_rand rand 0.9.3 7ec095654a25171c2124e9e3393a930bddbffdc939556c914957a4c3e0a87166 1aeee9f4c506f9f737c6c37c169ccdc365bfbabf src/seq/slice.rs src/seq/increasing_uniform.rs src/distr/uniform_int.rs Cargo.toml .cargo_vcs_info.json LICENSE-MIT LICENSE-APACHE
fetch_selected_crate rustc_rand_core rand_core 0.9.3 99d9a13982dcf210057a8a78572b2217b667c3beacbf3a0d8b454f6f82837d38 340849e53b71da0f15af448d10511c2e62e50ba1 src/lib.rs src/impls.rs src/le.rs Cargo.toml .cargo_vcs_info.json LICENSE-MIT LICENSE-APACHE
fetch_selected_crate rustc_rand_xoshiro rand_xoshiro 0.7.0 f703f4665700daf5512dcca5f43afa6af89f09db47fb56be587f80636bda2d41 242e4bdaf8d43a59d84c5511f427026026ea4c97 src/common.rs src/splitmix64.rs src/xoshiro128starstar.rs Cargo.toml .cargo_vcs_info.json LICENSE-MIT LICENSE-APACHE

if [[ "$(tr -d '\r\n' < "$ROOT/miri-source/rust-version")" != "$RUSTC_COMMIT" ]]; then
  printf 'Miri rust-version does not match the pinned rustc commit\n' >&2
  exit 1
fi
printf 'Pinned Miri, selected rustc, and rustc_apfloat sources are present and archive hashes match.\n'
