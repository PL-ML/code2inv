#!/bin/bash

# csvtool -t \| col 3 "$1" | sort -n
sed -ne "s/.*boogie_result': \([0-9]*\).*/\1/p" "$1"