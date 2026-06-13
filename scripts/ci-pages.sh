#!/usr/bin/env bash

set -euo pipefail

step() {
  printf '\n[ci-pages] %s\n' "$*" >&2
}

step "warming dependency cache"
python3 tools/verso-harness/scripts/ensure_dependency_cache.py --project-root . --warm-cache

step "building Main"
lake build +Main 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .

step "checking dependency cache after build"
python3 tools/verso-harness/scripts/ensure_dependency_cache.py --project-root .

step "generating site"
lake env lean --run Main.lean --output _out/site 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .

step "checking generated site"
python3 tools/verso-harness/scripts/check_generated_site.py --project-root . --site-dir _out/site/html-multi
