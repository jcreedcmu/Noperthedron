#!/bin/bash

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

while read lemma; do
    # this </dev/null is because of https://github.com/ggreer/the_silver_searcher/issues/943
    files=$(ag --nogroup "\[SY25\] $lemma"  -G '.lean$' . 2>/dev/null </dev/null)
    if [ -z "$files" ]; then
        echo -e "${RED}Missing: $lemma${NC}"
    else
        echo -e "${GREEN}Found $lemma in:${NC}"
        echo "$files"
    fi
done < scripts/lemmas.txt
