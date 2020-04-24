#!/bin/bash

sed -ne "s/.*actual_z3': \([0-9]*\).*/\1/p" "$1"