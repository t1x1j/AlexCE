#!/bin/bash
# Patch a stock CEdev v14.2 so OUTPUT_MAP=YES (wsl_build.sh) can write bin/DEMO.map for this app.
# The app's sections are located at .app.header.element (the OS picks the flash address at install
# time), so its symbols are "element + offset" and the map writer's output.hex stops on them
# ("cannot subdivide variable term"). Printing the constant term ("scale 0") gives the offset in
# the app for those and leaves plain numbers (RAM symbols, which tools/emu probes) unchanged.
# The binary is the same with or without the patch. Idempotent; keeps ld.alm.orig.
# Usage (WSL): patch_cedev_map.sh <CEdev dir>
set -euo pipefail
F="$1/meta/ld.alm"
grep -q 'compute value, value scale 0' "$F" && { echo "already patched"; exit 0; }
[ -f "$F.orig" ] || cp "$F" "$F.orig"
# The only output.hex in ld.alm: its first compute.
sed -i '/calminstruction output.hex value\*/,/loop:/s/compute value, value$/compute value, value scale 0/' "$F"
grep -q 'compute value, value scale 0' "$F" && echo "patched $F" || { echo "pattern not found in $F"; exit 1; }
