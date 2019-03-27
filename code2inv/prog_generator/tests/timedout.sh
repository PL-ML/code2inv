for i in $(ls tmp/*.err); do grep "TIME" $i 2>&1 > /dev/null && echo $i | sed 's/[^0-9]*//g' ; done
