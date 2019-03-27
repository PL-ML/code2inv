#!/bin/bash

echo Success-;for i in $(ls tmp/*.out); do grep "Success" $i 2>&1 > /dev/null && echo $i; done; echo Failed-;for i in $(ls tmp/*.out); do grep "Fail" $i 2>&1 > /dev/null && echo $i; done; echo "Timed Out-"; for i in $(ls tmp/*.err); do grep "TIME" $i 2>&1 > /dev/null && echo $i; done;

