#!/usr/bin/env bash
# A cache hit is usable only if every required binary resolves and runs.
set -euo pipefail

bin_dir="${1:?usage: check_foundry_installation.sh BIN_DIRECTORY}"
for tool in forge cast anvil; do
  [ -x "${bin_dir}/${tool}" ] || exit 1
  version="$("${bin_dir}/${tool}" --version)" || exit 1
  printf '%s\n' "$version" | grep -Eq "^${tool} Version: 1\\.5\\.0(-|$)" || exit 1
done
