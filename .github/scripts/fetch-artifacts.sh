#!/usr/bin/env bash
# fetch-artifacts.sh  download + extract ASan/UBSan artifact ZIPs.
#
# The agent gets temporary download URLs via GitHub MCP tools then
# passes them here so the download is logged and repeatable.
#
# usage: fetch-artifacts.sh <asan_url> [ubsan_url]
# output: /tmp/reports/{asan-reports,ubsan-reports}/

set -euo pipefail

REPORT_DIR="/tmp/reports"
LOG="/tmp/fetch-artifacts.log"

log() { printf '[%s] %s\n' "$(date -u +%H:%M:%S)" "$*" | tee -a "$LOG"; }

asan_url="${1:?usage: $0 <asan_url> [ubsan_url]}"
ubsan_url="${2:-}"

rm -rf "$REPORT_DIR"
mkdir -p "$REPORT_DIR/asan-reports" "$REPORT_DIR/ubsan-reports"
: > "$LOG"

download_and_extract() {
  local name=$1
  local url=$2
  local dest=$3
  local zip="/tmp/${name}.zip"

  log "$name: downloading"
  if ! curl -fsSL "$url" -o "$zip"; then
    log "$name: download failed (curl exit $?)"
    return 1
  fi
  log "$name: $(stat -c%s "$zip") bytes"

  unzip -oq "$zip" -d "$dest"
  log "$name: extracted $(ls -1 "$dest" | wc -l) files"
  ls -1 "$dest" | while read -r f; do log "  $f"; done
}

download_and_extract "asan" "$asan_url" "$REPORT_DIR/asan-reports"

if [ -n "$ubsan_url" ]; then
  download_and_extract "ubsan" "$ubsan_url" "$REPORT_DIR/ubsan-reports"
else
  log "ubsan: skipped (no url)"
fi

log "all done"
echo "$REPORT_DIR"
