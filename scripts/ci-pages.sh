#!/usr/bin/env bash

set -euo pipefail

lake build 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .
lake exe blueprint-gen --output _out/site 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-preview-manifest.json
