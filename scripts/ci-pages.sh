#!/usr/bin/env bash

set -euo pipefail

nice lake build blueprint-gen
rm -rf _out/site
lake exe blueprint-gen --output _out/site

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json
