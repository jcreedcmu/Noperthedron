#!/usr/bin/env bash
set -euo pipefail

REPO_URL="${RUPERT_REPO_URL:-https://github.com/Jakob256/Rupert.git}"
REF="${RUPERT_REF:-main}"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_DIR="${ROOT_DIR}/external/rupert"

mkdir -p "${OUT_DIR}/data"

commit="$(git ls-remote "${REPO_URL}" "${REF}" | awk '{print $1}')"
if [[ -z "${commit}" ]]; then
  echo "error: could not resolve ref '${REF}' from ${REPO_URL}" >&2
  exit 1
fi

echo "${commit}" > "${OUT_DIR}/REVISION"

raw_base="https://raw.githubusercontent.com/Jakob256/Rupert/${commit}/data"

download() {
  local name="$1"
  local url="${raw_base}/${name}"
  local out="${OUT_DIR}/data/${name}"
  echo "downloading ${name}..."
  curl -fsSL --retry 5 --retry-delay 2 -o "${out}" "${url}"
}

download "solution_tree.parquet"
download "mapping.csv"
download "Ck.csv"

echo "ok: downloaded Rupert data at ${OUT_DIR}"
echo "  revision: ${commit}"
echo "  files:"
ls -lh "${OUT_DIR}/data"
