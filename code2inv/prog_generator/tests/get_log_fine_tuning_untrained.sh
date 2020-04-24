filename="$1"

fileno=$(echo $filename | sed -n 's|.*tmp/\(.*\)\.out.*|\1|p')

stats=$(sed -n 's/.* stats: Counter(\(.*\))/\1/p' $filename)

# runningtime=$(sed -ne 's/.*z3_report time: \(.*\)pid.*/\1/p' $filename)

iterations=($(sed -ne 's|.*\| \(.*\)/100.*|\1|p' $filename))

totaliter=0
num_full_iter=$(($(grep "epoch" $filename | wc -l) - 2))
totaliter=$(($num_full_iter * 100 + ${iterations[-1]}))

inv="$(grep 'sol:' $filename)"

echo -e "$filename\n$inv\n--\n$totaliter\n$stats"
