#!/bin/bash

# A script to perform a comprehensive audit and verification of Dafny files

YELLOW='\033[1;33m'
GREEN='\033[0;32m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# Check if Dafny is installed
if ! command -v dafny &> /dev/null; then
    echo -e "${RED}Error: 'dafny' command not found. Please install Dafny and add it to your PATH.${NC}"
    exit 1
fi

echo -e "${YELLOW}Starting Dafny Formal Verification Audit...${NC}\n"

# Only check specific files if provided as arguments, otherwise check all .dfy files in src/
if [ "$#" -gt 0 ]; then
    FILES="$@"
else
    FILES=$(find src -name "*.dfy")
fi

if [ -z "$FILES" ]; then
    echo -e "${RED}No .dfy files found in the current directory.${NC}"
    exit 1
fi

for file in $FILES; do
    if [ ! -f "$file" ]; then
        echo -e "${RED}File not found: $file${NC}"
        continue
    fi

    echo -e "${GREEN}==========================================${NC}"
    echo -e "${GREEN}Auditing File: $file${NC}"
    echo -e "${GREEN}==========================================${NC}\n"

    echo -e "${YELLOW}1. Running Dafny Audit (Checking for unsoundness/assumes)...${NC}"
    dafny audit "$file"
    echo ""

    echo -e "${YELLOW}2. Running Strict Verification (with warnings enabled)...${NC}"
    dafny verify \
        --warn-shadowing \
        --warn-missing-constructor-parentheses \
        --track-print-effects \
        --enforce-determinism \
        "$file"
    echo ""

    echo -e "${YELLOW}3. Measuring Verification Complexity...${NC}"
    dafny measure-complexity "$file" | grep -v 'Starting verification of mutation'
    echo ""
done

echo -e "${GREEN}All checks completed!${NC}"
