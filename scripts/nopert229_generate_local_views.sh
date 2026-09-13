#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

artifact_dir=${1:-.artifacts/nopert229}
if [[ "$artifact_dir" != /* ]]; then
  artifact_dir="$repo_root/$artifact_dir"
fi
mkdir -p "$artifact_dir"

workers=${2:-8}
tube_radius="51/10000"
target_c="26/10000"
max_depth=28

echo "=== Generating Certified Local View Tables for Nopert #229 ==="
echo "Artifact Directory: $artifact_dir"
echo "Tube Radius:        $tube_radius (0.0051)"
echo "Target Margin c:    $target_c (0.0026)"
echo "Workers:            $workers"
echo "Max Depth:          $max_depth"

pack_local() {
  local index=$1
  local input=$2
  local output="$artifact_dir/local-view${index}.pack"
  echo "Packing $input -> $output..."
  python3 scripts/nopert214_emit_packed_local_view_lean.py \
    "$artifact_dir/$input" /dev/null \
    --table-index "$index" --namespace "GeneratedLocalView${index}Native" \
    --raw-output "$output.new" --raw-only
  mv -f "$output.new" "$output"
  echo "Packed local-view${index}.pack successfully."
}

for child in 0 1 2 3; do
  json_file="local-view-child${child}.json"
  echo ""
  echo "--- Processing Initial Child ${child} of Upper Wedge ---"
  python3 scripts/nopert229_certificate_search.py generate-projective-local-view-table \
    "$artifact_dir/$json_file" \
    --initial-child "$child" \
    --tube-radius "$tube_radius" \
    --target-c "$target_c" \
    --max-depth "$max_depth" \
    --workers "$workers" \
    --resume

  pack_local "$child" "$json_file"
done

echo ""
echo "=== All 4 local view tables generated and packed successfully! ==="
