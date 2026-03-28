#!/bin/bash

# Script to measure and analyze Dafny verification resource usage

YELLOW='\033[1;33m'
GREEN='\033[0;32m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m'

if ! command -v dafny &> /dev/null; then
    echo -e "${RED}Error: 'dafny' command not found.${NC}"
    exit 1
fi

if [ "$#" -eq 0 ]; then
    FILES=$(find src -name "*.dfy")
else
    FILES="$@"
fi

if [ -z "$FILES" ]; then
    echo -e "${RED}No .dfy files provided or found.${NC}"
    exit 1
fi

echo -e "${BLUE}=== Dafny Verification Resource Usage Analysis ===${NC}\n"

for file in $FILES; do
    if [ ! -f "$file" ]; then
        continue
    fi
    
    echo -e "${YELLOW}Analyzing File: $file${NC}"
    
    # Run measure-complexity and store the result
    # We grep out the "Starting verification..." spam lines
    OUTPUT=$(dafny measure-complexity "$file" 2>/dev/null | grep -v 'Starting verification of mutation')
    
    # Save IFS and enable loop per line
    while IFS= read -r line; do
        if [[ $line == *"consumed resources:"* ]] || [[ $line == *"The most demanding"* ]] || [[ $line == *"total consumed resources"* ]]; then
            echo -e "${BLUE}$line${NC}"
        elif [[ $line =~ (.*\.dfy\([0-9]+,[0-9]+\):)[[:space:]]*([0-9]+) ]]; then
            # Extract the file/line and the resource number
            LOC="${BASH_REMATCH[1]}"
            RES="${BASH_REMATCH[2]}"
            
            # Color code based on resource consumption
            # Using basic threshold heuristics:
            # > 1 000 000 : RED (very heavy verification task)
            # > 100 000   : YELLOW (moderate to heavy)
            # <= 100 000  : GREEN (light/normal)
            
            if [ "$RES" -gt 1000000 ]; then
                echo -e "$LOC \t ${RED}$RES ⚠️ (Heavy Task)${NC}"
            elif [ "$RES" -gt 100000 ]; then
                echo -e "$LOC \t ${YELLOW}$RES (Moderate Task)${NC}"
            else
                echo -e "$LOC \t ${GREEN}$RES${NC}"
            fi
        else
            # Print any other output lines normally
            if [ -n "$line" ]; then
                echo "$line"
            fi
        fi
    done <<< "$OUTPUT"
    echo ""
done

echo -e "${GREEN}Analysis Complete!${NC}"
echo -e "${NC}Hint: If tasks are marked as ${RED}Heavy${NC}, consider adding intermediate assertions/lemmas to help the verifier.${NC}"
